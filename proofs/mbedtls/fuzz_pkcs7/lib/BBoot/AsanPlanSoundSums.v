(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib
  AsanAcct AsanAcctShape SpinAlg Hoare.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanPopFree.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import StepGrows.     (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanPlanSoundSums () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.ret_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "Corelib.Lists.ListDef.repeat"; "APSX.kept_ok"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.None"; "APSX.Specs.SEALED_BYTES"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.env"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.expr"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.edenot"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.ridx"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.ELit"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3Sound.AX2S.regs_ok"; "Stdlib.Lists.List.NoDup"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.sr_fresh"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.EVar"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.NCS"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.ev"; "APSX.ext_call"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.caller_saved"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.sr_vars_lt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.expr_vars_lt"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Lists.ListDef.map"; "Corelib.Lists.ListDef.seq"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.kentry"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3Sound.AX2S.know_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kwritable"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3Sound.AX2S.estart"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.SA"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kwritable_x"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3Sound.AX2S.elenZ"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kzero_x"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.lres"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.know_lookup"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.sidecond"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.LHit"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3Sound.AX2S.flat"; "APSX.KnowTests.piece_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kread8e"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kreadZ"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kread_bytes"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.zbytes_le_to_Z"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.copy_facts"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.acs"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.cs_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.reg"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.reg_lit"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.two64"; "RocqVerifyHarness.AgentSubmission.ABoot.StoreOk.mem_grows"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kn_havoc"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.flat_x"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymRun3.env_agree"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.nxt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.fresh_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.pairs_vars_lt"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.a_vis"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.a_ghost"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.hid"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.sym_state"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanAcct.same_but_materialized"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanAcct.MInv"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.allowA"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.s_regs"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.sentry"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.s_log"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.Mr"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.s_know"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.with_ss"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanAcct.lazy_cover"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.a_ss"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kn_vars_lt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.kn"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.maps_vars_lt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.a_maps"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.a_brk"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.fd_vars_lt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.a_fd"; "RocqVerifyHarness.AgentSubmission.ABoot.ShapeAlg.TSet"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.pc"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.mk_ss"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.ABoot.SpinAlg.srealizes"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.cfg_of"; "APSX.Sound.ext_call2"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.ret_lit"; "APSX.fill_spec"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.node1_stmt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.always"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.summary_fill"; "APSX.miz_spec"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.x_memiszero"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.summary_miz"; "APSX.copy_spec"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.summary_copy"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.img_cov"; "APSX.istrncpy_spec"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.x_istrncpy"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.x_sealed"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.summary_istrncpy"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPopFree.pf_bytes"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.popfree_facts"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPopFree.popfree_spec"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.x_popfree"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.summary_popfree"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.x_stmt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.XIStrncpy"].


Module APSX.
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.

Section Specs.
Variable SEGS : list Segment.

(* [comment removed for export] *)
Definition fill_spec (entry cmax : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pmem0,P,(0.&40.)(1.(0.&8.))Ps,(0.&40.)Pc,(0.&40.)Pn,$2.Pregs,(3.&5.(0.&40.))Pret,(0.&40.)P,(4.=R3.)P,(5.(6.(7.&40.R6.)R4.)(8.+2.+40.))P,(9.$:.(;.VSEGS,R8.R7.(<.R5.))$=.)P,(5.(7.&40.R7.)O1.)P,(>.R5.)P,(9.(0.&40.)(?.R7.(10.&5.+1.$11.))R6.)P,(9.(0.&40.)(?.R8.(10.&5.+:.$11.))R;.)P,(9.(0.&40.)(?.R9.(10.&5.+;.$11.))R;.)P,(9.(0.&40.)(?.R:.(10.&5.+<.$11.))(12.&40.R;.))(13.(3.&5.(0.&40.))Lregs',(3.&5.(0.&40.))(14.(15.VSEGS,(16.$17.R<.(12.&40.O2.)R10.(18.VSEGS,))(16.$17.R1.R;.(19.R10.R?.(1:.(0.&8.)(12.&8.(7.&40.R>.))(<.R=.)))(18.VSEGS,)))(14.(1;.R<.R1.)(9.(0.&40.)(?.R1.(10.&5.+:.$11.))R?.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition copy_spec (entry : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pmem0,P,(0.&40.)(1.(0.&8.))Pdst,(0.&40.)Psrc,(0.&40.)Pn,$2.Pbs,(1<.(0.&8.))Pregs,(3.&5.(0.&40.))Pret,(0.&40.)P,(4.=R4.)P,(9.$1=.(1>.(0.&8.)R4.)(<.R5.))P,(9.(1.(1<.(0.&8.)))(1?.VSEGS,R9.R7.(1>.(0.&8.)R5.))(20.(1<.(0.&8.))R5.))P,(9.$:.(;.VSEGS,R:.R9.(1>.(0.&8.)R6.))$=.)P,(21.(4.(6.(7.&40.R:.)R8.)(7.&40.R9.))(4.(6.(7.&40.R9.)R8.)(7.&40.R:.)))P,(5.(6.(7.&40.R:.)R9.)(8.+2.+40.))P,(5.(6.(7.&40.R<.)R:.)(8.+2.+40.))P,(>.R8.)P,(9.(0.&40.)(?.R:.(10.&5.+1.$11.))R9.)P,(9.(0.&40.)(?.R;.(10.&5.+:.$11.))R?.)P,(9.(0.&40.)(?.R<.(10.&5.+;.$11.))R?.)P,(9.(0.&40.)(?.R=.(10.&5.+<.$11.))(12.&40.R?.))(13.(3.&5.(0.&40.))Lregs',(3.&5.(0.&40.))(14.(15.VSEGS,(16.$17.R?.(12.&40.O1.)R14.(18.VSEGS,))(16.$17.R1.R>.(19.R14.R13.R10.)(18.VSEGS,)))(14.(1;.R?.R1.)(9.(0.&40.)(?.R1.(10.&5.+:.$11.))R13.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition miz_spec (entry : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pmem,P,(0.&40.)(1.(0.&8.))Pbeg,(0.&40.)Psp,(0.&40.)PN,$2.Pregs,(3.&5.(0.&40.))Pret,(0.&40.)P,(14.(4.=R3.)(4.R3.(8.+2.+28.)))P,(4.(6.(6.(7.&40.R6.)R4.)+8.)(8.+2.+40.))P,(4.+10.(7.&40.R6.))P,(9.$:.(;.VSEGS,R9.(12.&40.(22.(7.&40.R7.)+8.))#8.)$=.)P,(21.(4.(6.(7.&40.R9.)R7.)(22.(7.&40.R8.)+8.))(4.(7.&40.R8.)(7.&40.R9.)))P,Pa,(0.&40.)P,(14.(4.(7.&40.R;.)(7.&40.R1.))(5.(7.&40.R1.)(6.(7.&40.R;.)R9.)))(9.(1.(1<.(0.&8.)))(1?.VSEGS,R=.R2.#1.)(20.(1<.(0.&8.))(23.(0.&8.)(12.&8.=)(24.(0.&8.)))))P,(>.R7.)P,(9.(0.&40.)(?.R9.(10.&5.+1.$11.))R8.)P,(9.(0.&40.)(?.R:.(10.&5.+2.$11.))R<.)P,(9.(0.&40.)(?.R;.(10.&5.+:.$11.))R>.)P,(9.(0.&40.)(?.R<.(10.&5.+;.$11.))(12.&40.R=.))(13.(3.&5.(0.&40.))Lregs',(3.&5.(0.&40.))(14.(15.VSEGS,(16.$17.R>.(12.&40.O1.)R12.(18.VSEGS,))(16.$17.R1.R=.(19.R12.(12.&40.(22.(7.&40.R10.)+8.))(25.#8.R=.))(18.VSEGS,)))(14.(1;.R>.R1.)(9.(0.&40.)(?.R1.(10.&5.+:.$11.))(12.&40.+1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SEALED_BYTES : list byte := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "(26.(0.&8.)(23.(0.&8.)(12.&8.+3<.)(23.(0.&8.)(12.&8.+73.)(23.(0.&8.)(12.&8.+65.)(23.(0.&8.)(12.&8.+61.)(23.(0.&8.)(12.&8.+6<.)(23.(0.&8.)(12.&8.+65.)(23.(0.&8.)(12.&8.+64.)(23.(0.&8.)(12.&8.+3>.)(24.(0.&8.))))))))))(1:.(0.&8.)(12.&8.=)#??7.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition istrncpy_spec (entry src : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pmem0,Px,(0.&40.)(1.(0.&8.))Pdst,(0.&40.)Pregs,(3.&5.(0.&40.))Pret,(0.&40.)P,Pi,$2.P,(14.(4.O1.R1.)(5.R1.(6.O1.+9.)))(9.(1.(0.&8.))A1.R6.(12.&40.R2.)(27.(0.&8.)))P,(9.$:.(;.VSEGS,R5.R4.#???.)$=.)P,(5.(6.(7.&40.R5.)+???.)(8.+2.+40.))P,(21.(4.(6.(7.&40.R6.)+???.)O1.)(4.(6.O1.+9.)(7.&40.R6.)))P,(>.R5.)P,(9.(0.&40.)(?.R7.(10.&5.+1.$11.))R6.)P,(9.(0.&40.)(?.R8.(10.&5.+:.$11.))R9.)P,(9.(0.&40.)(?.R9.(10.&5.+;.$11.))(12.&40.O1.))P,(9.(0.&40.)(?.R:.(10.&5.+<.$11.))(12.&40.+???.))(13.(3.&5.(0.&40.))Lregs',(3.&5.(0.&40.))(14.(15.VSEGS,(16.$17.R<.(12.&40.O2.)R>.(18.VSEGS,))(16.$17.R1.R;.(19.R>.R=.$28.)(18.VSEGS,)))(14.(1;.R<.R1.)(9.(0.&40.)(?.R1.(10.&5.+:.$11.))R=.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Psr,(1<.$2:.)PR,(3.&5.(0.&40.))P,Pr,(0.&5.)P,(2;.(9.(0.&5.)R1.(10.&5.=$11.)))(9.(0.&40.)(?.R3.R2.)(2<.R5.(2=.$2:.(2>.R2.)R4.(2?.=))))(30.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pcs0,(1<.$1=.)Pnx,$1=.Psr,(1<.$2:.)Pj,$1=.P,(31.$1=.R4.)P,(32.R2.(1>.$1=.R5.))(9.$2:.(2=.$2:.(2=.$1=.R3.R6.#0.)(33.R4.R6.R5.)(2?.=))(34.(35.R5.R3.)))")
(* [comment removed for export] *).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Pnx,$1=.PR',(3.&5.(0.&40.))Pj,$1=.P,(32.R1.$36.)(9.(0.&40.)(37.(38.R5.R4.R3.)(35.R4.R2.))(?.R3.(12.&5.(39.(2=.$1=.R2.$3:.#0.)))))")
(* [comment removed for export] *).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pb,$1=.Psr,(1<.$2:.)Pr,$1=.P,(9.$:.(3;.R3.R2.)$=.)P,(32.R2.#20.)(9.$:.(3<.R5.(2=.$2:.R3.R4.(2?.=)))$=.)")
(* [comment removed for export] *).
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> kept_ok R R' ->
  match rv with Some e => AP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
  { destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    - destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X. }
  destruct rv as [e|]; [|exact GEN].
  destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
  rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
  rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_same : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pbs,(1<.(0.&8.))Pm,Px,(0.&40.)(1.(0.&8.))Pa,(0.&40.)P,(4.(6.(7.&40.R1.)(39.(1>.(0.&8.)R3.)))(8.+2.+40.))P,Pj,$1=.P,(32.R1.(1>.(0.&8.)R5.))(9.(1.(0.&8.))A1.R5.(12.&40.(6.(7.&40.R4.)(39.R2.)))(20.(0.&8.)(2=.(0.&8.)R2.R6.(12.&8.=))))(9.P,(0.&40.)(1.(0.&8.))(19.R4.R3.R5.)R4.)")
(* [comment removed for export] *).
Proof.
  intros bs m a Hnw Hall. apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  { apply wbytes_out; [exact Hnw | lia]. }
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
  2: { apply wbytes_out; [exact Hnw | lia]. }
  set (j := Z.to_nat (bv_unsigned x - bv_unsigned a)).
  assert (Hxj : x = Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
  { subst j. rewrite Z2Nat.id by lia. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
    symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Hxj at 1. rewrite wbytes_nth by lia. rewrite Hxj. symmetry. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_defined : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pbs,(1<.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pj,$1=.P,(4.(6.(7.&40.R2.)(39.(1>.(0.&8.)R4.)))(8.+2.+40.))P,(32.R2.(1>.(0.&8.)R5.))(2;.(9.(1.(0.&8.))(19.R5.R4.R6.(12.&40.(6.(7.&40.R4.)(39.R3.))))(27.(0.&8.))))")
(* [comment removed for export] *).
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_all : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Psegs,(1<.$3=.)Pm,Px,(0.&40.)(1.(0.&8.))Pn,$1=.Pa,(0.&40.)Pb,(0.&8.)P,(4.(6.(7.&40.R2.)(39.R3.))(8.+2.+40.))P,Pi,$2.P,(14.(4.=R1.)(5.R1.(39.R5.)))(9.(1.(0.&8.))A1.R7.(12.&40.(6.(7.&40.R5.)R2.))(20.(0.&8.)R4.))(9.(1.(1<.(0.&8.)))(1?.R7.R6.R4.R5.)(20.(1<.(0.&8.))(1:.(0.&8.)R3.R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat].
  pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b); [reflexivity | rewrite Hu1; lia |].
    intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_nth : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Psegs,(1<.$3=.)Pm,P,(0.&40.)(1.(0.&8.))Pn,$1=.Pa,(0.&40.)Pbs,(1<.(0.&8.))Pj,$1=.P,(4.(6.(7.&40.R3.)(39.R4.))(8.+2.+40.))P,(9.(1.(1<.(0.&8.)))(1?.R7.R6.R4.R5.)(20.(1<.(0.&8.))R3.))P,(32.R3.R6.)(9.(1.(1<.(0.&8.)))(1?.R9.R8.(12.&40.(6.(7.&40.R6.)(39.R4.)))#1.)(20.(1<.(0.&8.))(23.(0.&8.)(2=.(0.&8.)R4.R5.(12.&8.=))(24.(0.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
  destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
  destruct j as [|j'].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
  - cbn [nth]. destruct n as [|n'']; [lia|].
    assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
    apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_of_nth : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Psegs,(1<.$3=.)Pm,P,(0.&40.)(1.(0.&8.))Pn,$1=.Pa,(0.&40.)Pf,P,$1=.(0.&8.)P,(4.(6.(7.&40.R2.)(39.R3.))(8.+2.+40.))P,Pj,$1=.P,(32.R1.R5.)(9.(1.(1<.(0.&8.)))(1?.R8.R7.(12.&40.(6.(7.&40.R5.)(39.R2.)))#1.)(20.(1<.(0.&8.))(23.(0.&8.)A1.R4.R2.(24.(0.&8.)))))(9.(1.(1<.(0.&8.)))(1?.R7.R6.R4.R5.)(20.(1<.(0.&8.))(3>.$1=.(0.&8.)R3.(3?.#0.R5.))))")
(* [comment removed for export] *).
Proof.
  intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
  cbn [rdn seq map].
  pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection H0 as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pa,$2.Pb,$2.Pk,$2.P,(4.=R3.)P,(4.=R2.)P,(14.(4.=R4.)(5.R4.(8.+2.R3.)))(9.$2.(40.(41.R6.(8.+2.R4.))R5.)(6.(41.R6.(8.+2.R4.))R5.))")
(* [comment removed for export] *).
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pbs,(1<.(0.&8.))P,(42.(1>.(0.&8.)R1.)#8.)(9.(1<.(0.&8.))(25.(1>.(0.&8.)R2.)(12.&40.(43.R2.)))R2.)")
(* [comment removed for export] *).
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma word_to_le_bytes_of_bytes_n : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pn,$1=.Pbs,(1<.(0.&8.))P,(9.$1=.(1>.(0.&8.)R1.)R2.)P,(42.R3.#8.)(9.(1<.(0.&8.))(25.R4.(12.&40.(43.R3.)))R3.)")
(* [comment removed for export] *).
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KnowTests.
Variable segs : list Segment.

#[using="Type"] Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kwritable_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pallkn,(1<.$44.)Pk,(1<.$44.)Pb,$2:.Poff,$2.Pn,$2.P,(45.Vsegs,R7.R6.R5.)P,(45.Vsegs,R8.R7.R5.)P,(9.$:.(46.R7.R6.R5.R4.R3.)$=.)P,(4.=R4.)(14.(9.$:.(;.Vsegs,R:.(12.&40.(47.R;.(48.R7.R6.)))(<.R5.))$=.)(14.(4.=(47.R;.(48.R7.R6.)))(4.(6.(47.R;.(48.R7.R6.))R5.)(8.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable] in H.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
  { intros A B. split; [|lia].
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
    pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
  - lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
    apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
    apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
    destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
    unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kwritable_x_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pallkn,(1<.$44.)Pk,(1<.$44.)Pb,$2:.Poff,$2.Pn,$2:.P,(45.Vsegs,R7.R6.R5.)P,(45.Vsegs,R8.R7.R5.)P,(9.$:.(49.R7.R6.R5.R4.R3.)$=.)(14.Pm,$1=.P,(4.(39.R1.)(4:.R;.R5.))(9.$:.(;.Vsegs,R;.(12.&40.(47.R<.(48.R8.R7.)))R2.)$=.)(14.(4.=(47.R:.(48.R6.R5.)))(4.(6.(47.R:.(48.R6.R5.))(4:.R:.R4.))(8.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kzero_x_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pallkn,(1<.$44.)Pk,(1<.$44.)Pb,$2:.Poff,$2.Pn,$2:.P,(45.Vsegs,R7.R6.R5.)P,(45.Vsegs,R8.R7.R5.)P,(9.$:.(4;.R7.R6.R5.R4.R3.)$=.)(14.Pi,$2.P,(14.(4.=R1.)(5.R1.(4:.R;.R5.)))(9.(1.(0.&8.))A1.R;.(12.&40.(6.(47.R<.(48.R8.R7.))R2.))(20.(0.&8.)(12.&8.=)))(14.(4.=(47.R:.(48.R6.R5.)))(4.(6.(47.R:.(48.R6.R5.))(4:.R:.R4.))(8.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n zb zk zn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kimg_cut_sound : forall E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- context [KImg ?l ?h] => rename l into lo; rename h into hi end.
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition piece_ok (E : env) (M : word -> option byte) (b : expr) (off : Z) (w : nat) (v : expr) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "(13.(1<.(0.&8.))Lbs,(1<.(0.&8.))(14.(9.(1.(1<.(0.&8.)))(1?.Vsegs,O5.(12.&40.(47.O6.(48.O4.O3.)))O2.)(20.(1<.(0.&8.))R1.))(14.(9.$1=.(1>.(0.&8.)R1.)O2.)(9.(1<.(0.&8.))(25.O2.(2<.O6.O1.))R1.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma lookup_piece : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Pb,$2:.Poff,$2.Pw,$1=.Pv,$2:.Phs,(1<.$:.)P,(45.Vsegs,R8.R7.R6.)P,(14.(42.#1.R4.)(42.R4.#8.))P,(9.$4<.(4=.Vsegs,R8.R7.R6.R5.$4>.(24.$:.)(24.$4?.))(50.R4.(24.$4?.)R3.))P,(51.R;.(48.R8.R7.)(39.R6.))(52.R<.R;.R9.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros E M k b off w v hs HK Hw HL Hfl.
  pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
  unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.

#[using="Type"] Lemma kread8e_piece : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Pb,$2:.Poff,$2.Pv,$2:.P,(45.Vsegs,R6.R5.R4.)P,(9.(1.$2:.)(53.Vsegs,R5.R4.R3.)(20.$2:.R2.))P,(51.R8.(48.R5.R4.)+8.)(52.R9.R8.R6.R5.#8.R4.)")
(* [comment removed for export] *).
Proof.
  intros E M k b off v HK H Hfl. unfold kread8e in H.
  destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.

#[using="Type"] Lemma kreadZ1_byte : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Pb,$2:.Poff,$2.Pz,$2.P,(45.Vsegs,R6.R5.R4.)P,(9.(1.$2.)(54.Vsegs,R5.R4.R3.#1.)(20.$2.R2.))P,(51.R8.(48.R5.R4.)+1.)(14.(9.(1.(1<.(0.&8.)))(1?.Vsegs,R8.(12.&40.(47.R9.(48.R6.R5.)))#1.)(20.(1<.(0.&8.))(23.(0.&8.)(12.&8.R4.)(24.(0.&8.)))))(14.(4.=R4.)(5.R4.+100.)))")
(* [comment removed for export] *).
Proof.
  intros E M k b off z HK H Hfl. unfold kreadZ in H.
  destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  destruct bs as [|b0 [|]]; try discriminate.
  cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
  pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
  split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

#[using="Type"] Lemma kread_bytes_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Plen,$1=.Pb,$2:.Poff,$2.Pzs,(1<.$2.)P,(45.Vsegs,R7.R6.R5.)P,(9.(1.(1<.$2.))(55.Vsegs,R5.R6.R4.R3.)(20.(1<.$2.)R2.))P,(4.=(47.R9.(48.R5.R4.)))P,(4.(6.(47.R:.(48.R6.R5.))(39.R7.))(8.+2.+40.))(14.(9.(1.(1<.(0.&8.)))(1?.Vsegs,R:.(12.&40.(47.R;.(48.R7.R6.)))R8.)(20.(1<.(0.&8.))(3>.$2.(0.&8.)Lz,$2.(12.&8.R1.)R5.)))(14.(9.$1=.(1>.$2.R5.)R8.)(56.$2.Lz,$2.(14.(4.=R1.)(5.R1.+100.))R5.)))")
(* [comment removed for export] *).
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
  - cbn [kread_bytes] in H.
    destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
    destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
    destruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
                 ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall).
    split; [| split; [cbn; lia | constructor; assumption]].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app; [exact Hrd|].
    replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
    apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
    rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma zbytes_of_small : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pzs,(1<.$2.)P,(56.$2.Lz,$2.(14.(4.=R1.)(5.R1.+100.))R1.)(9.$2.(57.R2.)(43.(3>.$2.(0.&8.)Lz,$2.(12.&8.R1.)R2.)))")
(* [comment removed for export] *).
Proof.
  intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
  induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma copy_facts_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Psb,$2:.Pdb,$2:.Pfuel,$1=.Psk,$2.Pdk,$2.Pn,$2.Pkc,(1<.$44.)P,(45.Vsegs,R:.R9.R8.)P,(9.(1.(1<.$44.))(58.Vsegs,R6.R9.R8.R5.R7.R4.R3.)(20.(1<.$44.)R2.))P,(4.=R4.)P,(42.(<.R5.)R8.)P,(4.=(47.R>.(48.R;.R8.)))P,(4.(6.(47.R?.(48.R<.R9.))R7.)(8.+2.+40.))P,(4.=(47.R10.(48.R<.R9.)))P,(4.(6.(47.R11.(48.R=.R:.))R9.)(8.+2.+40.))(13.(1<.(0.&8.))Lbs,(1<.(0.&8.))(14.(9.$1=.(1>.(0.&8.)R1.)(<.R;.))(14.(9.(1.(1<.(0.&8.)))(1?.Vsegs,R12.(12.&40.(47.R13.(48.R10.R=.)))(<.R;.))(20.(1<.(0.&8.))R1.))PM',P,(0.&40.)(1.(0.&8.))P,(9.(1.(1<.(0.&8.)))(1?.Vsegs,R1.(12.&40.(47.R14.(48.R10.R=.)))(<.R<.))(20.(1<.(0.&8.))R2.))(45.Vsegs,R15.R2.R<.))))")
(* [comment removed for export] *).
Proof.
  intros E M k sb db fuel. induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
  - cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
    exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
  - cbn [copy_facts] in H.
    (* [comment removed for export] *)
    assert (STEP : forall (w : nat) v kr,
      (1 <= w <= 8)%nat -> Z.of_nat w <= n ->
      piece_ok E M sb sk w v ->
      copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
      kc = KWord (SA db dk) w v :: kr ->
      exists bs, length bs = Z.to_nat n
        /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
        /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
    { intros w v kr Hw Hwn (bsP & HrdP & HlenP & HvP) Hr ->.
      assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      destruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
        as (bsR & HlenR & HrdR & HKR).
      exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
      - replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
        apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
        rewrite ES in HrdR.
        replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
      - intros M' HM'. constructor.
        + cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
          rewrite adenot_SA, HvP.
          pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
          rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
        + apply HKR. rewrite ED.
          pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
          replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
          replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
          2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
          rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
    + apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
      destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
        [|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
      assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
      destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
      * injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
      * destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
        apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
        destruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall).
        exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
        cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
        replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
        apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
    + clear H8. destruct (Z.leb 1 n) eqn:H1.
      * apply Z.leb_le in H1.
        destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
        destruct scs; [|discriminate].
        destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
        injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
      * injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
        exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.

End KnowTests.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable SP0 : Z.                        (* [comment removed for export] *)
Hypothesis SP0_ok : APS.sp0_ok SP0.
Hypothesis argH_high : forall E (a : word), argH E a = true -> SP0 <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,Px,(0.&40.)(1.(0.&8.))PM',Px,(0.&40.)(1.(0.&8.))P,Pa,(0.&40.)P,(9.$:.A2.VargH,R4.R1.$=.)(9.(1.(0.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(0.&40.)P,(4.VSP0,(7.&40.R1.))P,(2;.(9.(1.(0.&8.))A1.R5.R2.(27.(0.&8.))))(2;.(9.(1.(0.&8.))A1.R5.R3.(27.(0.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_sp : forall E M, SINV E M -> APS.uE_sp0 E = SP0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.

#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SP0 SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A SP0 argH) (only parsing).
#[local] Notation MR := (Mr A SP0 argH) (only parsing).

(* [comment removed for export] *)
#[local] Ltac aps_fill :=
  first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
        | exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT].

#[using="Type"] Lemma w_reg_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Pcs,$59.PR,(3.&5.(0.&40.))PFULL,P,(0.&40.)(1.(0.&8.))Pmodel,$5:.Pn,$1=.P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R6.R5.R4.R3.R2.)P,(14.(32.#0.R2.)(32.R2.#20.))(9.(0.&40.)(?.R6.(12.&5.(39.R3.)))(2<.R8.(5<.R7.R3.)))")
(* [comment removed for export] *).
Proof. intros. eapply reg_sound; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="Type"] Lemma w_reg_lit_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Pcs,$59.PR,(3.&5.(0.&40.))PFULL,P,(0.&40.)(1.(0.&8.))Pmodel,$5:.Pn,$1=.Pz,$2.P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R7.R6.R5.R4.R3.)P,(14.(32.#0.R3.)(32.R3.#20.))P,(9.(1.$2.)(5=.R8.R4.)(20.$2.R3.))(14.(9.(0.&40.)(?.R8.(12.&5.(39.R5.)))(12.&40.R4.))(14.(4.=R4.)(5.R4.$5>.)))")
(* [comment removed for export] *).
Proof. intros. eapply reg_lit_sound; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="Type"] Lemma w_split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof. intros. eapply split_lit_denot; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="Type"] Lemma w_know_ok_havoc : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))PM',Px,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Pb,$2:.Po,$2.Pn,$2:.P,(45.VSEGS,R7.R6.R4.)P,Px,(0.&40.)P,(21.(5.(7.&40.R1.)(47.R9.(48.R5.R4.)))(4.(6.(47.R9.(48.R5.R4.))(4:.R9.R3.))(7.&40.R1.)))(9.(1.(0.&8.))A1.R8.R2.A1.R9.R2.)P,(5?.R8.R7.)(45.VSEGS,R:.R8.(60.R7.R6.R5.R4.))")
(* [comment removed for export] *).
Proof. intros. eapply know_ok_havoc; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="Type"] Lemma w_flat_x_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Pb,$2:.Poff,$2.Pn,$2:.P,(45.VSEGS,R6.R5.R4.)P,(9.$:.(61.R5.R4.R3.R2.)$=.)(14.(4.=(47.R8.(48.R5.R4.)))(14.(4.(6.(47.R8.(48.R5.R4.))(7.&40.(2<.R8.R3.)))(8.+2.+40.))(5.=(7.&40.(2<.R8.R3.)))))")
(* [comment removed for export] *).
Proof. intros. eapply flat_x_sound; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="Type"] Lemma w_env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [Hv Hb] Hle. split; [|exact Hb]. intros n Hn. apply Hv. lia. Qed.

#[using="argH_agree SINV_agree"] Lemma w_cs_ok_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PE',$29.Pcs,$59.PR,(3.&5.(0.&40.))PFULL,P,(0.&40.)(1.(0.&8.))Pmodel,$5:.P,(62.(63.R4.)R6.R5.)P,(9.$:.(64.Vnx0,R5.)$=.)P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R8.R6.R5.R4.R3.)(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. intros. eapply cs_ok_agree; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="argH_agree"] Lemma w_hid_agree : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pb,$1=.PE,$29.PE',$29.Pcs,$59.Pmodel,$5:.P,(62.R5.R4.R3.)P,(42.Vnx0,R6.)P,(9.$:.(65.R7.(26.(66.$2:.$2:.)(67.R4.)(68.R4.)))$=.)(9.Pa,(0.&40.)$:.(69.VA,VSP0,VargH,R6.R5.R4.)(69.VA,VSP0,VargH,R7.R5.R4.))")
(* [comment removed for export] *).
Proof. intros. eapply hid_agree; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="SINV_frame"] Lemma w_cs_ok_frame : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Pcs,$59.PR,(3.&5.(0.&40.))PFULL,P,(0.&40.)(1.(0.&8.))Pmodel,$5:.Pss',$6:.PR',(3.&5.(0.&40.))PFULL',P,(0.&40.)(1.(0.&8.))Pmodel',$5:.P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R9.R8.R7.R6.R5.)P,(6;.R6.R2.)P,(6<.(6=.VA,R;.R:.)R3.)P,(30.R<.(6>.R7.)R6.)P,(9.(1<.$6?.)(70.R8.)(24.$6?.))P,(45.VSEGS,R>.(71.VA,VSP0,VargH,R>.R=.R:.R7.)(72.R9.))P,Pa,(0.&40.)P,(9.$:.(69.VA,VSP0,VargH,R10.R?.R<.R1.)$=.)(9.(1.(0.&8.))A1.R:.R2.A1.R>.R2.)P,Pa,(0.&40.)P,(2;.(9.(1.(0.&8.))A1.R>.R1.(27.(0.&8.))))(2;.(9.(1.(0.&8.))A1.R;.R2.(27.(0.&8.))))(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R11.(73.R10.R<.)R;.R:.R9.)")
(* [comment removed for export] *).
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="nx0 HULL_ok"] Lemma w_lazy_cover_cs : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Pcs,$59.PR,(3.&5.(0.&40.))PFULL,P,(0.&40.)(1.(0.&8.))Pmodel,$5:.P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R5.R4.R3.R2.R1.)(74.(69.VA,VSP0,VargH,R6.R5.R2.)(75.R2.)(6=.VA,R6.R5.))")
(* [comment removed for export] *).
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="nx0"] Lemma w_A_wf_allowA : forall E cs, A_wf (allowA A E cs).
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="SEGS_in_hull HULL_ok SP0_ok argH_high"] Lemma w_H_off_segments_cs : forall E cs model, H_off_segments SEGS (HID E cs model).
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.

#[using="Type"] Lemma w_fresh_ok_parts : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pcs,$59.P,(9.$:.(64.Vnx0,R1.)$=.)(14.(9.$:.(3;.(63.R2.)(6>.(76.R2.)))$=.)(14.(9.$:.(77.(63.R2.)(78.R2.))$=.)(14.(9.$:.(79.(63.R2.)(7:.R2.))$=.)(14.(9.$:.(65.(63.R2.)(26.(66.$2:.$2:.)(67.R2.)(68.R2.)))$=.)(14.(9.$:.(3<.(63.R2.)(7;.R2.))$=.)(14.(9.$:.(7<.(63.R2.)(7=.R2.))$=.)(42.Vnx0,(63.R2.))))))))")
(* [comment removed for export] *).
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma find_segment_In : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
#[using="SEGS_wr"] Lemma wview_rd1 : forall M (a : word) b,
  wview SEGS M a = Some b ->
  (match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
Proof.
  intros M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  destruct (seg_writable seg) eqn:Hw; [|discriminate].
  rewrite (SEGS_wr seg (find_segment_In _ _ _ _ Hf) Hw).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
Qed.

#[using="SEGS_wr"] Lemma store_ok_rdn : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pn,$1=.PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)P,(4.(6.(7.&40.R1.)(39.R3.))(8.+2.+40.))P,(9.$:.(;.VSEGS,R3.R2.R4.)$=.)(13.(1<.(0.&8.))Lbs,(1<.(0.&8.))(14.(9.(1.(1<.(0.&8.)))(1?.VSEGS,R5.R4.R6.)(20.(1<.(0.&8.))R1.))(9.$1=.(1>.(0.&8.)R1.)R6.)))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros M a Hnw Hst.
  - exists []. split; reflexivity.
  - cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
    cbn [rdn]. rewrite (wview_rd1 M a b Hv).
    destruct n as [|n'].
    + exists [b]. split; reflexivity.
    + assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen).
      rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma call_core_R : forall (SR : config -> TSet -> Prop), APS.srchain SEGS SR ->   (* [comment removed for export] *)
  forall cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
  CSOK E cs R FULL model ->
  fresh_ok nx0 cs = true ->
  env_agree (nxt cs) E E' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  regs_ok E' sr2 regs' ->
  know_ok SEGS E' MR' k' ->
  (forall R' FULL' model',
      CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
      SR (cfg R' ret FULL' model') T) ->
  SR (cfg R (pc cs) FULL model) T.
Proof.
  intros SR SRch cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hk.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (H := HID E cs model).
  unfold cfg_of.
  apply (SRch H
           (w_H_off_segments_cs E cs model) SEGS_wx (allowA A E cs)
           (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
           (w_lazy_cover_cs E cs R FULL model HC)
           (w_A_wf_allowA E cs)
           (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
  - rewrite restrict_mkst. exact Hms.
  - intros model' Hinv' Hsame Hclean.
    set (FULL' := munrestrict H FULL MR').
    change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
      with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
    apply (Hk regs' FULL' model').
    + pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
      pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
      eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
      * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
      * exact HR'.
      * reflexivity.
      * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
        fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
        exact HK'.
      * intros a Ha. rewrite HH in Ha.
        unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
      * (* [comment removed for export] *)
        intros a Hdef. unfold FULL', munrestrict. destruct (H a) eqn:Ha; [exact Hdef|].
        pose proof (msteps_mem_grows SEGS _ _ Hms) as G. cbn [ms_mem mkst] in G. apply G.
        unfold Mr, mrestrict. fold H. rewrite HH || idtac. rewrite Ha. exact Hdef.
    + apply (same_but_materialized_frame _ _ Hsame).
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma call_core : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pcs,$59.PE,$29.PE',$29.PR,(3.&5.(0.&40.))PFULL,P,(0.&40.)(1.(0.&8.))Pmodel,$5:.PT,$7>.Pret,$2.Psr2,(1<.$2:.)Pk',(1<.$44.)Pnx2,$1=.Pregs',(3.&5.(0.&40.))PMR',P,(0.&40.)(1.(0.&8.))P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R<.R=.R:.R9.R8.)P,(9.$:.(64.Vnx0,R>.)$=.)P,(62.(63.R?.)R>.R=.)P,(15.VSEGS,(16.$17.R=.(12.&40.(7?.R10.))(71.VA,VSP0,VargH,R?.R10.R;.R<.)(18.VSEGS,))(16.$17.R5.(12.&40.R9.)R4.(18.VSEGS,)))P,(30.R?.R9.R6.)P,(45.VSEGS,R10.R6.R9.)P,PR',(3.&5.(0.&40.))PFULL',P,(0.&40.)(1.(0.&8.))Pmodel',$5:.P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R14.(73.R16.(80.R?.R>.R=.R<.))R3.R2.R1.)P,(9.$81.(82.R2.)(82.R12.))(83.VSEGS,(84.VSEGS,R5.R11.R4.R3.)R12.)(83.VSEGS,(84.VSEGS,R11.(7?.R14.)R10.R?.)R>.)")
(* [comment removed for export] *).
Proof. exact (call_core_R (srealizes SEGS) (APS.srchain_srealizes SEGS)). Qed.

#[using="Type"] Lemma sr_vars_lt_fresh : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Prs,(1<.$1=.)Psr,(1<.$2:.)Pnx,$1=.Pb,$1=.P,(9.$:.(3;.R1.R3.)$=.)P,(42.(35.R3.(1>.$1=.R5.))R2.)(9.$:.(3;.R3.(33.R5.R6.R4.))$=.)")
(* [comment removed for export] *).
Proof.
  induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
  apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma call_node_sound_R : forall (SR : config -> TSet -> Prop), APS.srchain SEGS SR ->   (* [comment removed for export] *)
  forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
  CSOK E cs R FULL model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E MR' k' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      SR (cfg R' (pc cs') FULL' model') T) ->
  SR (cfg R (pc cs) FULL model) T.
Proof.
  intros SR SRch cs cs' E R FULL model T ret rv k' regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
  unfold after_call in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call E (nxt cs) regs').
  pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  eapply (call_core_R SR SRch cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms).
  - apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma call_node_sound : forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
  CSOK E cs R FULL model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E MR' k' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof. exact (call_node_sound_R (srealizes SEGS) (APS.srchain_srealizes SEGS)). Qed.

(* [comment removed for export] *)
Definition ext_call2 (E : env) (nx : nat) (R' : bvmap 5 word) (vals : list word) : env :=
  ext_list (ext_call E nx R') (nx + NCS) vals.

#[using="Type"] Lemma ext_call2_agree : forall E nx R' vals, env_agree nx E (ext_call2 E nx R' vals).
Proof.
  intros E nx R' vals. unfold ext_call2.
  destruct (ext_call_agree E nx R') as [H1 H2]. destruct (ext_list_agree (ext_call E nx R') (nx + NCS) vals) as [H3 H4].
  split; [|rewrite H2; exact H4]. intros n Hn. rewrite H1 by exact Hn. apply H3. lia.
Qed.

#[using="Type"] Lemma ext_call2_agree16 : forall E nx R' vals, env_agree (nx + NCS) (ext_call E nx R') (ext_call2 E nx R' vals).
Proof. intros. unfold ext_call2. apply ext_list_agree. Qed.

#[using="Type"] Lemma ext_call2_at : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Pnx,$1=.PR',(3.&5.(0.&40.))Pvals,(1<.(0.&40.))Pi,$1=.P,(32.R1.(1>.(0.&40.)R2.))(9.(0.&40.)(37.(85.R6.R5.R4.R3.)(35.(35.R5.$36.)R2.))(2=.(0.&40.)R2.R3.(12.&40.=)))")
(* [comment removed for export] *).
Proof. intros. unfold ext_call2. apply ext_list_at. assumption. Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma call_node_sound2 : forall cs cs' E R FULL model T (ret : Z) rv k' extra vals regs' MR',
  CSOK E cs R FULL model ->
  after_call2 nx0 cs ret rv k' extra = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS (ext_call2 E (nxt cs) regs' vals) MR' k' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' extra vals regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
  unfold after_call2 in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call2 E (nxt cs) regs' vals).
  pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
  set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
  assert (Hsf : AP.sr_vars_lt (nxt cs + NCS) sr1 = true).
  { subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
    unfold caller_saved, NCS. cbn [length]. lia. }
  assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
  { eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
    - destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
    - subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
      destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
  eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms HR2 HK').
  intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
  split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ret_lit_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.Pcs,$59.PR,(3.&5.(0.&40.))PFULL,P,(0.&40.)(1.(0.&8.))Pmodel,$5:.Pr,$2.P,(5;.VSEGS,VA,VLIMIT,VSP0,VSINV,VargH,VFS0,R6.R5.R4.R3.R2.)P,(9.(1.$2.)(86.R6.)(20.$2.R2.))(14.(9.(0.&40.)(?.R6.(12.&5.+1.))(12.&40.R3.))(14.(>.(12.&40.R3.))(14.(4.=R3.)(5.R3.$5>.))))")
(* [comment removed for export] *).
Proof.
  intros E cs R FULL model r HC H. unfold ret_lit in H.
  destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (w_reg_sound E cs R FULL model 1 HC ltac:(lia)) as R1.
  rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.


#[using="Type"] Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> AP.expr_vars_lt m e = true -> AP.expr_vars_lt m b = true.
Proof.
  intros e b k m H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

#[using="Type"] Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
  intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.

#[using="Type"] Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma k0_sound : forall E M k db dk ne dst k0,
  know_ok SEGS E M k ->
  (if off_image_x A k db dk ne then Some k
   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) = Some k0 ->
  know_ok SEGS E M k0.
Proof.
  intros E M k db dk ne dst k0 HK H.
  destruct (off_image_x A k db dk ne); [injection H as <-; exact HK|].
  destruct dst; try discriminate. destruct ne; try discriminate. injection H as <-.
  apply kimg_cut_sound. exact HK.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_fill_at : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PM,P,(0.&40.)(1.(0.&8.))Ps,(0.&40.)Pb,(0.&8.)Pn,$2.Pi,$2.P,(4.(6.(7.&40.R4.)R2.)(8.+2.+40.))P,(14.(4.=R2.)(5.R2.R3.))(9.(1.(0.&8.))(19.R7.R6.(1:.(0.&8.)R5.(<.R4.))(12.&40.(6.(7.&40.R6.)R3.)))(20.(0.&8.)R5.))")
(* [comment removed for export] *).
Proof.
  intros M s b n i Hnw Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.

#[using="Type"] Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 (c mod 256) = Z_to_bv 8 c.
Proof.
  intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma summary_fill_sound_R : forall (SR : config -> TSet -> Prop), APS.srchain SEGS SR ->   (* [comment removed for export] *)
  forall entry cmax,
  fill_spec SEGS entry cmax ->
  APS.node1_stmt_R SEGS A nx0 LIMIT SP0 SINV argH FS0 SR always (fun cs => summary_fill A nx0 cs entry cmax).
Proof.
  intros SR SRch entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_fill_eq in Hn. (* [comment removed for export] *) unfold summary_fill_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
  destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k',
     store_ok SEGS M s (Z.to_nat n) = true ->
     know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     SR (cfg R (pc cs) FULL model) T).
  { intros k' Hst HK' Hac.
    destruct (SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
                 ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
      as (regs' & Hms & Hkept & Ha0).
    rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
    eapply (call_node_sound_R SR SRch cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
  assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
  { apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _).
    rewrite Hse, Hlen in *.
    apply (FIN (kn cs)); [apply Wst; lia | | exact Hn].
    destruct (Z.eq_dec n 0) as [Hz|Hnz]; [rewrite (WB0 Hz); exact HKN|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    rewrite wbytes_same; [exact HKN | rewrite repeat_length; lia |].
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
    rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
  clear Hzb.
  (* [comment removed for export] *)
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
  destruct (kwritable_x (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
  rewrite Hse, Hlen in *.
  eapply FIN; [apply Wst; lia | | exact Hn].
  set (M' := wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))).
  assert (HK1 : know_ok SEGS E M' (kn_havoc k0 db dk (reg cs 12))).
  { eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. destruct (Z.eq_dec n 0) as [Hz|Hnz]; [subst M'; rewrite (WB0 Hz); reflexivity|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    subst M'. apply wbytes_out; rewrite repeat_length; lia. }
  destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HK1]. apply Z.ltb_lt in Hpos.
  assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
  assert (FILL : forall i, 0 <= i < n -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (Z_to_bv 8 c)).
  { intros i Hi. subst M'. rewrite <- Hus. apply wbytes_fill_at; lia. }
  constructor; [|exact HK1].
  destruct (Z.eqb (c mod 256) 0) eqn:Hc8; cbn [kentry_ok]; rewrite Hlen.
  - apply Z.eqb_eq in Hc8. split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity.
  - split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite Z_to_bv8_mod. reflexivity.
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma summary_fill_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pentry,$2.Pcmax,$2.P,(87.VSEGS,R2.R1.)(88.VSEGS,VA,Vnx0,VLIMIT,VSP0,VSINV,VargH,VFS0,$89.Lcs,$59.(8:.VA,Vnx0,R1.R4.R3.))")
(* [comment removed for export] *).
Proof. exact (summary_fill_sound_R (srealizes SEGS) (APS.srchain_srealizes SEGS)). Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma store_ok_sub : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PM,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,$1=.Pb,(0.&40.)Pm,$1=.P,(4.(6.(7.&40.R4.)(39.R3.))(8.+2.+40.))P,(9.$:.(;.VSEGS,R6.R5.R4.)$=.)P,(4.(7.&40.R6.)(7.&40.R4.))P,(4.(6.(7.&40.R5.)(39.R4.))(6.(7.&40.R7.)(39.R6.)))(9.$:.(;.VSEGS,R9.R6.R5.)$=.)")
(* [comment removed for export] *).
Proof.
  intros M a n b m Hnw Hst Hlo Hhi. apply store_ok_of_all; [lia|].
  intros x Hx. eapply (store_ok_all SEGS M n a Hnw Hst). lia.
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma summary_miz_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "P,(8;.VSEGS,(8<.VA,))(88.VSEGS,VA,Vnx0,VLIMIT,VSP0,VSINV,VargH,VFS0,$89.Lcs,$59.(8=.VA,Vnx0,R1.))")
(* [comment removed for export] *).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_miz_eq in Hn. (* [comment removed for export] *) unfold summary_miz_ref in Hn.
  destruct (Z.eqb (pc cs) (x_memiszero A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eaddz (reg cs 2) (-16))) as [qb qk] eqn:Hsq.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hwr]. apply andb_prop in Hcond as [Hcond Hsphi'].
  apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hb8].
  apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.leb_le in Hb8. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'.
  unfold two64 in Hb8, Hsphi'.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (beg := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *.
  set (nw := edenot E (reg cs 11)) in *. set (N := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold N in Hnr. pose proof (u64_range beg) as Hbr. pose proof (u64_range spw) as Hsr.
  assert (HnwN : Z_to_bv 64 N = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HlenN : elenZ E (reg cs 11) = N) by reflexivity.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold spw in Hq. unfold v_add in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = bv_unsigned spw - 16).
  { apply (f_equal bv_unsigned) in Hq. rewrite !u_lit64 in Hq. unfold two64 in Hq.
    change (estart E (SA qb qk)) with Q in Hq.
    rewrite (Z.mod_small Q) in Hq by lia.
    rewrite <- Hq.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (Hstk : store_ok SEGS M (Z_to_bv 64 (bv_unsigned spw - 8)) 8 = true).
  { apply (store_ok_sub M (Z_to_bv 64 Q) 16); rewrite ?u64_lit by lia; try lia. exact Qst. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 10) bb bk Hsb) as Hbeg. fold beg in Hbeg.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (reg cs 11) HKN HKN Hkz) as (Zb & Blo & Bhi).
  rewrite HlenN in Zb, Bhi.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) qb qk (ELit 16) bb bk (reg cs 11) HKN Hap) as Hapart.
  rewrite HlenN in Hapart. change (estart E (SA qb qk)) with Q in Hapart.
  replace (elenZ E (ELit 16)) with 16 in Hapart by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  set (B := estart E (SA bb bk)) in *.
  assert (HuB : bv_unsigned beg = B \/ (B = 2 ^ 64 /\ bv_unsigned beg = 0)).
  { destruct (Z.eq_dec B (2 ^ 64)) as [HB|HB].
    - right. split; [exact HB|]. rewrite Hbeg. change (bv_unsigned (edenot E bb) + bk) with B. rewrite HB. reflexivity.
    - left. rewrite Hbeg. apply u64_lit. lia. }
  assert (Hdisj : bv_unsigned beg + N <= bv_unsigned spw - 8 \/ bv_unsigned spw <= bv_unsigned beg) by lia.
  assert (Hz : forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
                 rdn SEGS M a 1 = Some [Z_to_bv 8 0]).
  { intros a Ha. apply rdn1_overlay.
    destruct HuB as [HuB|[HB Hu0]]; [|lia].
    replace a with (Z_to_bv 64 (B + (bv_unsigned a - B))) by (rewrite <- (Z_to_bv_bv_unsigned 64 a) at 2; f_equal; lia).
    apply Zb. lia. }
  destruct (SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
               ltac:(rewrite HnwN; exact R11)) as (regs' & Hms & Hkept & Ha0).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (ELit 1)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 16)) with 16 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
  - exact Hk.
Qed.

(* [comment removed for export] *)

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree SEGS_wr"] Lemma summary_copy_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "Pentry,$2.P,(8>.VSEGS,R1.)(88.VSEGS,VA,Vnx0,VLIMIT,VSP0,VSINV,VargH,VFS0,$89.Lcs,$59.(8?.VSEGS,VA,Vnx0,R1.R3.))")
(* [comment removed for export] *).
Proof.
  intros entry SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_copy_eq in Hn. (* [comment removed for export] *) unfold summary_copy_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  remember (reg cs 12) as ne eqn:Hne.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
  pose proof (w_split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
  assert (Hlen : elenZ E ne = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k' bs,
     length bs = Z.to_nat n ->
     rdn SEGS M sr (length bs) = Some bs ->
     store_ok SEGS M s (length bs) = true ->
     (bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
     know_ok SEGS E (wbytes M s bs) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros k' bs Hlbs Hrd Hst Hdisj HK' Hac.
    destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn]. }
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
  apply andb_prop in Hwa as [Hwr Hap].
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  rewrite Hse in Wst.
  (* [comment removed for export] *)
  assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
            know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
  { intros bs Hlbs Hpos.
    assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
    eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
    apply wbytes_out; rewrite Hlbs; lia. }
  (* [comment removed for export] *)
  assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
  { intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
  (* [comment removed for export] *)
  assert (VARS : fresh_ok nx0 cs = true ->
            AP.kn_vars_lt (nxt cs) (kn cs) = true /\ AP.expr_vars_lt (nxt cs) db = true /\ AP.expr_vars_lt (nxt cs) ne = true
            /\ AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
  { intros Hfresh. destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & _).
    split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
    eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  (* [comment removed for export] *)
  assert (GEN : kwritable_x (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
    forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
    after_call2 nx0 cs ret (Some (reg cs 10))
      (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
       ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
      = Some cs' ->
    srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros Hswr Hsfl W u HW Hu Hac.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi).
    destruct (w_flat_x_sound E M (kn cs) sb sk ne HKN Hsfl) as (_ & _ & Spos).
    rewrite Hlen in SWst, Shi. change (bv_unsigned (edenot E ne)) with n in Spos.
    change (estart E (SA sb sk)) with S in SWst, Slo, Shi. rewrite Hsre in SWst.
    destruct (HusD Spos Slo Shi) as [Hus Husr].
    destruct (store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia))) as (bs & Hrd & Hlbs).
    assert (Hfresh : fresh_ok nx0 cs = true).
    { unfold after_call2 in Hac. destruct (fresh_ok nx0 cs); [reflexivity | cbn [andb] in Hac; discriminate]. }
    destruct (VARS Hfresh) as (Fkn & Fdb & Fne & Fsr).
    destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
                 ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 W)).
    eapply (call_node_sound2 cs cs' E R FULL model T ret (Some (reg cs 10)) _ W vals regs' (wbytes M s bs) HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - set (E2 := ext_call2 E (nxt cs) regs' vals).
      pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag2. fold E2 in Hag2.
      assert (Edb : edenot E2 db = edenot E db) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fdb]).
      assert (Ene : edenot E2 ne = edenot E ne) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fne]).
      assert (ED2 : estart E2 (SA db dk) = D) by (unfold estart; cbn [a_base a_off]; rewrite Edb; reflexivity).
      assert (EL2 : elenZ E2 ne = n) by (unfold elenZ; rewrite Ene; reflexivity).
      pose proof (rdn_wbytes_hit SEGS bs M s ltac:(rewrite Hlbs; lia)) as Hhit.
      apply Forall_app. split.
      + (* [comment removed for export] *)
        apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
        assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = D + 8 * Z.of_nat i).
        { unfold estart. cbn [a_base a_off]. rewrite Edb. change (estart E (SA db dk)) with (bv_unsigned (edenot E db) + dk) in *. unfold D. unfold estart. cbn [a_base a_off]. lia. }
        cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
        rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
        subst vals. rewrite (nth_map_seq _ W i (Z_to_bv 64 0)) by lia.
        assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
        rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
        pose proof (rdn_skipn SEGS (wbytes M s bs) (length bs) s bs (8 * i) Hhit ltac:(lia)) as Sk.
        pose proof (rdn_firstn SEGS (wbytes M s bs) (length bs - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
        replace (Z_to_bv 64 (D + 8 * Z.of_nat i)) with (s + nat_to_word (8 * i))%bv; [exact Fi|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, Hus.
        rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
      + apply Forall_app. split.
        { (* [comment removed for export] *)
          unfold kblob_prefix.
          destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
          apply find_some in HF as [HinK HKt].
          destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | |]; try (now constructor).
          apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
          apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
          pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
          assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          rewrite En0 in HKB. destruct HKB as (Bflat & Blen & Bbytes).
          change (estart E (SA sb sk)) with S in Bflat, Bbytes.
          destruct Hag2 as [Hag2a Heb2].
          assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) (ELit n0) j));
            [| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
          cbn [kentry_ok]. rewrite En0', ED2, <- Heb2.
          refine (conj _ (conj Blen _)).
          - unfold flat. rewrite ED2. unfold flat in Bflat. pose proof (Wlo) as Wlo'. pose proof (Whi) as Whi'.
            change (estart E (SA db dk)) with D in Wlo', Whi'. lia.
          - intros i Hi. rewrite <- Hus.
            replace i with (Z.of_nat (Z.to_nat i)) by lia.
            rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia).
            f_equal.
            pose proof (rdn_nth SEGS M (Z.to_nat n) sr bs (Z.to_nat i) ltac:(lia) Hrd ltac:(lia)) as RB1.
            rewrite Husr in RB1. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
            cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
          }
      (* [comment removed for export] *)
        assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
        pose proof (k0_sound E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
        assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
        { eapply w_know_ok_havoc; [exact HK02 | | apply wbytes_grows].
          intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
        destruct u; [|exact HAV2].
        constructor; [|exact HAV2].
        (* [comment removed for export] *)
        apply know_ok_unk_intro_pt.
        * unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
        * intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
          replace i with (Z.of_nat (Z.to_nat i)) by lia.
          apply wbytes_defined; rewrite Hlbs; lia.
    - exact Hk. }
  (* [comment removed for export] *)
  assert (HSRC :
    (if (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
     then after_call2 nx0 cs ret (Some (reg cs 10))
            (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
                 (seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
             ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
            (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
     else None) = Some cs' ->
    srealizes SEGS (cfg R (pc cs) FULL model) T).
  { destruct (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
    apply andb_prop in Hsw as [Hswr Hsfl].
    assert (Hu : Z.ltb 0 nlo = true -> 0 < n) by (intros Hnlo0; apply Z.ltb_lt in Hnlo0; lia).
    destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:HW.
    - apply andb_prop in HW as [HW Hp]. apply andb_prop in HW as [HW H256]. apply andb_prop in HW as [Heq Hm8].
      apply Z.eqb_eq in Heq. apply Z.eqb_eq in Hm8. apply Z.leb_le in H256. apply Z.ltb_lt in Hp.
      apply (GEN Hswr Hsfl); [|exact Hu].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - apply (GEN Hswr Hsfl); [lia | exact Hu]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
  { apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi).
    rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
    destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
    apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
      [apply repeat_length | | | lia | | exact Hn].
    - rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
    - rewrite repeat_length. apply Wst. lia.
    - constructor; [| apply HAVOC; [apply repeat_length | lia]].
      cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
      intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
  clear Hzs.
  (* [comment removed for export] *)
  destruct ne as [z| | | | | | |]; try exact (HSRC Hn).
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc3; [|exact (HSRC Hn)] end.
  apply andb_prop in Hc3 as [H2048 Hfl]. apply Z.leb_le in H2048.
  destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf; [|exact (HSRC Hn)].
  assert (Hnn : n = nhi).
  { cbn [xhi] in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. subst n nw. cbn [edenot]. apply u_lit64. }
  destruct (w_flat_x_sound E M (kn cs) sb sk (ELit z) HKN Hfl) as (Slo & Shi & Spos).
  change (estart E (SA sb sk)) with S in Slo, Shi. change (bv_unsigned (edenot E (ELit z))) with n in Shi, Spos.
  destruct (HusD Spos Slo Shi) as [Hus Husr].
  destruct (copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
              ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
              ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))
    as (bs & Hlbs & Hrd & HKC).
  change (estart E (SA sb sk)) with S in Hrd. change (estart E (SA db dk)) with D in HKC.
  rewrite <- Hnn in Hlbs, Hrd, HKC.
  apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn].
  - rewrite Hlbs, <- Hsre. exact Hrd.
  - rewrite Hlbs. apply Wst. lia.
  - apply Forall_app. split.
    + apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
    + apply HAVOC; [exact Hlbs | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma img_cov_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Pk,(1<.$44.)Pa,$2.Pb,$2.P,(45.VSEGS,R5.R4.R3.)P,(9.$:.(90.R4.R3.R2.)$=.)Pi,$2.P,(14.(4.R5.R1.)(5.R1.R4.))(9.(1.(0.&8.))A1.R8.(12.&40.R2.)(27.(0.&8.)))")
(* [comment removed for export] *).
Proof.
  intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
  destruct K as [| | |lo hi| | | | | |]; try discriminate.
  apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. destruct HK1 as (_ & _ & HK1).
  apply HK1. lia.
Qed.

#[using="Type"] Lemma SEALED_BYTES_length : length SEALED_BYTES = 4095%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma SEALED_W_bytes : word_to_le_bytes 8 (Z_to_bv 64 SEALED_W) = firstn 8 SEALED_BYTES.
Proof.
  replace SEALED_W with (bytes_le_to_Z (firstn 8 SEALED_BYTES)) by (vm_compute; reflexivity).
  apply word_to_le_bytes_of_bytes_n; reflexivity.
Qed.

#[using="Type"] Lemma SEALED_BYTES_nth_hi : forall j, (8 <= j < 4095)%nat -> nth j SEALED_BYTES (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros j Hj. unfold SEALED_BYTES. rewrite app_nth2 by (cbn; lia). cbn [length]. apply nth_repeat_lt. lia.
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma summary_istrncpy_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "P,(91.VSEGS,(92.VA,)(93.VA,))(88.VSEGS,VA,Vnx0,VLIMIT,VSP0,VSINV,VargH,VFS0,$89.Lcs,$59.(94.VA,Vnx0,R1.))")
(* [comment removed for export] *).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_istrncpy_eq in Hn. (* [comment removed for export] *) unfold summary_istrncpy_ref in Hn.
  destruct (Z.eqb (pc cs) (x_istrncpy A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [src|] eqn:H11; [|discriminate].
  destruct (reg_lit cs 12) as [n|] eqn:H12; [|discriminate].
  destruct (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool eqn:Hsn; [|discriminate]. cbn [negb] in Hn.
  apply andb_prop in Hsn as [Hsrc Hn95]. apply Z.eqb_eq in Hsrc. apply Z.eqb_eq in Hn95. subst src n.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  rename Hcond into Hb. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  match goal with Hl : Z.leb 0 (x_sealed A) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hs0 end.
  match goal with Hl : Z.ltb (x_sealed A + 9) two64 = true |- _ => apply Z.ltb_lt in Hl; unfold two64 in Hl; rename Hl into Hs9 end.
  match goal with Hl : kwritable_x _ _ db dk (ELit 4095) = true |- _ => rename Hl into Hwr end.
  match goal with Hl : img_cov k0 _ _ = true |- _ => rename Hl into Hcov end.
  match goal with Hl : ranges_apart_x _ db dk (ELit 4095) (ELit 0) _ (ELit 9) = true |- _ => rename Hl into Hap end.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (w_reg_lit_sound E cs R FULL model 11 _ HC ltac:(lia) H11) as [R11 _].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *.
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  pose proof (k0_sound E M (kn cs) db dk (ELit 4095) (reg cs 10) k0 HKN
                ltac:(destruct (off_image_x A (kn cs) db dk (ELit 4095)); [exact Hk0 | destruct (reg cs 10); try discriminate; exact Hk0])) as HK0.
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9) HKN Hap) as Hapart.
  rewrite !elenZ_lit in * by lia.
  unfold estart in Hapart at 2 3; cbn [a_base a_off edenot] in Hapart. rewrite u_lit0 in Hapart.
  set (D := estart E (SA db dk)) in *.
  assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
  pose proof (img_cov_sound E M k0 _ _ HK0 Hcov) as Hnone.
  destruct (SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
               Hrok R1 R10 R11 R12) as (regs' & Hms & Hkept & Ha0).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - set (M' := wbytes M s SEALED_BYTES).
    assert (Hlen : bv_unsigned s + Z.of_nat (length SEALED_BYTES) <= 2 ^ 64) by (rewrite SEALED_BYTES_length; lia).
    assert (BY : forall j, (j < 4095)%nat -> M' (Z_to_bv 64 (D + Z.of_nat j)) = Some (nth j SEALED_BYTES (Z_to_bv 8 0))).
    { intros j Hj. subst M'. rewrite <- Hus. apply wbytes_nth; [exact Hlen | rewrite SEALED_BYTES_length; exact Hj]. }
    constructor; [|constructor].
    + (* [comment removed for export] *)
      cbn [kentry_ok]. split; [lia|]. split; [unfold flat; cbn [Z.of_nat]; fold D; lia|].
      rewrite adenot_SA. fold D. rewrite <- Hus, Z_to_bv_bv_unsigned.
      cbn [edenot]. rewrite SEALED_W_bytes.
      replace (firstn 8 SEALED_BYTES) with (map (fun j => nth j SEALED_BYTES (Z_to_bv 8 0)) (seq 0 8)) by reflexivity.
      apply rdn_of_nth; [lia|]. intros j Hj. apply rdn1_overlay. rewrite Hus. apply BY. lia.
    + (* [comment removed for export] *)
      cbn [kentry_ok]. rewrite elenZ_lit by lia.
      assert (HD8 : estart E (SA db (dk + 8)) = D + 8) by (unfold D, estart; cbn [a_base a_off]; lia).
      rewrite HD8. split; [unfold flat; lia|].
      intros i Hi. replace (D + 8 + i) with (D + Z.of_nat (Z.to_nat (8 + i))) by lia.
      rewrite BY by lia. f_equal. apply SEALED_BYTES_nth_hi. lia.
    + (* [comment removed for export] *)
      eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite ?SEALED_BYTES_length; lia.
  - exact Hk.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma firstn_skipn_map_nth : forall {T} (d : T) k (l : list T) m, (m + k <= length l)%nat ->
  firstn k (skipn m l) = map (fun q => nth (m + q)%nat l d) (seq 0 k).
Proof.
  intros T d k. induction k as [|k IH]; intros l m Hm; [reflexivity|].
  cbn [seq map]. rewrite <- seq_shift, map_map.
  destruct (skipn m l) as [|x rest] eqn:Hs.
  - exfalso. pose proof (f_equal (@length _) Hs) as HL. rewrite length_skipn in HL. cbn in HL. lia.
  - cbn [firstn]. f_equal.
    + rewrite <- nth_skipn, Hs. reflexivity.
    + replace rest with (skipn (S m) l).
      2: { replace (S m) with (1 + m)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity. }
      rewrite (IH l (S m)) by lia. apply map_ext. intros q. f_equal. lia.
Qed.

#[using="Type"] Lemma popfree_facts_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "PE,$29.PM,P,(0.&40.)(1.(0.&8.))Plb,$2:.Plk,$2.Pcnt,$2.Pc,$2.Ps,$2.PK,$1=.Pbase,(0.&40.)P,(9.$2.(7.&40.R1.)(47.R9.(48.R7.R6.)))P,(42.R3.(<.R6.))P,(5.=R7.)P,(4.(6.(47.R<.(48.R:.R9.))(41.+4.R8.))(8.+2.+40.))P,(4.=(47.R=.(48.R;.R:.)))(45.VSEGS,R>.(19.R=.R6.(95.R9.R8.(<.R:.)))(96.R<.R;.R:.R9.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros E M lb lk cnt c s K base Hbase HK Hcnt Hhi Hlo. unfold popfree_facts. apply Forall_forall. intros Kx Hin.
  apply in_map_iff in Hin as [t [<- Hint]]. apply in_seq in Hint.
  set (D := estart E (SA lb lk)) in *. set (j := cnt - 1 - Z.of_nat t).
  assert (Hj : 0 <= j < cnt) by lia.
  cbn [kentry_ok]. split; [lia|].
  assert (HDj : estart E (SA lb (lk + 4 * j)) = D + 4 * j) by (unfold D, estart; cbn [a_base a_off]; lia).
  split; [unfold flat; rewrite HDj; cbn [Z.of_nat]; lia|].
  rewrite adenot_SA, HDj. cbn [edenot].
  rewrite word_to_le_bytes4_Z.
  replace ((c + Z.of_nat t * s) / 16) with ((c + (Z.of_nat (Z.to_nat cnt) - 1 - j) * s) / 16) by (f_equal; f_equal; lia).
  rewrite <- (pf_bytes_cell c s (Z.to_nat cnt) j) by lia.
  assert (Hlen : length (pf_bytes c s (Z.to_nat cnt)) = (4 * Z.to_nat cnt)%nat) by apply pf_bytes_length.
  rewrite (firstn_skipn_map_nth (Z_to_bv 8 0) 4) by (rewrite Hlen; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (D + 4 * j)) = D + 4 * j) by (apply u64_lit; lia).
  apply rdn_of_nth; [rewrite Hu; lia|]. intros q Hq. apply rdn1_overlay. rewrite Hu.
  replace (D + 4 * j + Z.of_nat q) with (bv_unsigned base + Z.of_nat (Z.to_nat (4 * j) + q)) by lia.
  apply wbytes_nth; rewrite Hlen; lia.
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma summary_popfree_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "P,(97.VSEGS,(98.VA,))Pargs,(1<.$2:.)(88.VSEGS,VA,Vnx0,VLIMIT,VSP0,VSINV,VargH,VFS0,$89.Lcs,$59.(99.VA,Vnx0,R1.R2.))")
(* [comment removed for export] *).
Proof.
  intros SUM args cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  unfold summary_popfree in Hn.
  destruct (Z.eqb (pc cs) (x_popfree A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct args as [|[K| | | | | | |] [|]]; try discriminate.
  destruct (reg_lit cs 10) as [i|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 12) as [c|] eqn:H12; [|discriminate].
  destruct (reg_lit cs 21) as [s|] eqn:H21; [|discriminate].
  destruct (reg_lit cs 19) as [n|] eqn:H19; [|discriminate].
  destruct (split_lit (eaddz (reg cs 11) (- (4 * n)))) as [lb lk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 11)) as [el|] eqn:Hel; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [eh|] eqn:Heh; [|discriminate].
  match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  apply Z.leb_le in Hcond.
  repeat match goal with
         | Hl : Z.leb _ _ = true |- _ => apply Z.leb_le in Hl
         | Hl : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hl end.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  match goal with Hl : fresh_ok nx0 cs = true |- _ => rename Hl into Hfresh end.
  match goal with Hl : kwritable_x _ _ lb lk _ = true |- _ => rename Hl into Hwr end.
  match type of Hn with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear Hn.
  (* [comment removed for export] *)
  destruct (w_reg_lit_sound E cs R FULL model 10 _ HC ltac:(lia) H10) as [R10 Hi].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 Hc].
  destruct (w_reg_lit_sound E cs R FULL model 21 _ HC ltac:(lia) H21) as [R21 Hs].
  destruct (w_reg_lit_sound E cs R FULL model 19 _ HC ltac:(lia) H19) as [R19 Hnn].
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hel) as Hel'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Heh) as Heh'.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  set (ew := edenot E (reg cs 11)) in *. set (e := bv_unsigned ew) in *.
  pose proof (u64_range ew) as Her. fold e in Her.
  set (cnt := n - i) in *.
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr) as (Wst & Wlo & Whi).
  rewrite elenZ_lit in Wst, Whi by lia.
  set (D := estart E (SA lb lk)) in *.
  pose proof (w_split_lit_denot E _ lb lk Hspl) as Hsd.
  assert (HloD : edenot E (eaddz (reg cs 11) (- (4 * n))) = Z_to_bv 64 (e - 4 * n)).
  { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64. fold ew. rewrite u_lit64. unfold two64.
    rewrite u64_lit by lia. fold e.
    replace (e + - (4 * n) mod 2 ^ 64) with ((e - 4 * n) + 1 * 2 ^ 64).
    2: { rewrite <- (Z.mod_add (- (4 * n)) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HD : D = e - 4 * n).
  { assert (HDdef : D = bv_unsigned (edenot E lb) + lk) by reflexivity.
    rewrite HloD, <- HDdef in Hsd. apply (f_equal bv_unsigned) in Hsd. rewrite !u64_lit in Hsd by lia. lia. }
  destruct (SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(rewrite <- HD; apply Wst; lia)) as (regs' & Hms & G10 & G12 & G14 & G15 & Gkeep).
  set (M' := wbytes M (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) in *.
  eapply (call_core cs E E R FULL model T (pc cs + 32) _ _ (nxt cs) regs' M' HC Hfresh (env_agree_refl _ _)).
  (* [comment removed for export] *)
  4: { intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' Hfs). }
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC r) as HR. unfold sr_get in HR.
    assert (Hrz : bv_eqb r 0%bv = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros Hc0. apply Hr0. apply bv_eq. exact Hc0. }
    rewrite Hrz in HR.
    destruct (Nat.eqb (ridx r) 15) eqn:E15.
    { apply Nat.eqb_eq in E15. rewrite (reg_of_ridx r 15 E15). refine (eq_trans G15 _). rewrite HloD. reflexivity. }
    destruct (Nat.eqb (ridx r) 14) eqn:E14.
    { apply Nat.eqb_eq in E14. rewrite (reg_of_ridx r 14 E14). refine (eq_trans G14 _). cbn [edenot]. f_equal; f_equal; lia. }
    destruct (Nat.eqb (ridx r) 12) eqn:E12.
    { apply Nat.eqb_eq in E12. rewrite (reg_of_ridx r 12 E12). refine (eq_trans G12 _). cbn [edenot]. f_equal; lia. }
    destruct (Nat.eqb (ridx r) 10) eqn:E10.
    { apply Nat.eqb_eq in E10. rewrite (reg_of_ridx r 10 E10). refine (eq_trans G10 _). reflexivity. }
    apply Nat.eqb_neq in E15. apply Nat.eqb_neq in E14. apply Nat.eqb_neq in E12. apply Nat.eqb_neq in E10.
    rewrite Gkeep; [exact HR| | | |]; intros Hrr; [apply E10 | apply E12 | apply E14 | apply E15]; rewrite Hrr; reflexivity.
  - (* [comment removed for export] *)
    assert (Hlen : length (pf_bytes c s (Z.to_nat (n - i))) = (4 * Z.to_nat cnt)%nat) by (unfold cnt; apply pf_bytes_length).
    assert (Hbase : bv_unsigned (Z_to_bv 64 (e - 4 * n)) = D) by (rewrite HD; apply u64_lit; lia).
    unfold know_ok. apply Forall_app_intro; [|apply Forall_app_intro].
    + fold cnt. apply (popfree_facts_sound E M lb lk cnt c s (Z.to_nat K) (Z_to_bv 64 (e - 4 * n)) Hbase); lia.
    + destruct (Z.ltb K cnt) eqn:HKc; [|constructor]. apply Z.ltb_lt in HKc.
      constructor; [|constructor]. cbn [kentry_ok]. rewrite elenZ_lit by lia. split; [unfold flat; lia|].
      intros q Hq. fold D. replace (D + q) with (bv_unsigned (Z_to_bv 64 (e - 4 * n)) + Z.of_nat (Z.to_nat q)) by lia.
      subst M'. apply wbytes_defined; rewrite Hlen; lia.
    + eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite Hlen; lia.
Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem node_x_sound_XIMemset :
  fill_spec SEGS (x_imemset A) 256 -> x_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 XIMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

(* [comment removed for export] *)
#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem node_x_sound0_XIMemset :
  fill_spec SEGS (x_imemset A) 256 -> x_stmt0 SEGS A nx0 LIMIT SP0 SINV argH FS0 XIMemset.
Proof. intros SUM args. exact (summary_fill_sound_R (srealizes0 SEGS) (APS.srchain_srealizes0 SEGS) _ _ SUM). Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem node_x_sound_XMemset :
  fill_spec SEGS (x_memset A) two64 -> x_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 XMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree SEGS_wr"] Theorem node_x_sound_XIMemcpy :
  copy_spec SEGS (x_imemcpy A) -> x_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 XIMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree SEGS_wr"] Theorem node_x_sound_XMemcpy :
  copy_spec SEGS (x_memcpy A) -> x_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 XMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem node_x_sound_XMemIsZero :
  miz_spec SEGS (x_memiszero A) -> x_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 XMemIsZero.
Proof. intros SUM args. exact (summary_miz_sound SUM). Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem node_x_sound_XIStrncpy : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSoundSums ()) "P,(91.VSEGS,(92.VA,)(93.VA,))(9:.VSEGS,VA,Vnx0,VLIMIT,VSP0,VSINV,VargH,VFS0,$9;.)")
(* [comment removed for export] *).
Proof. intros SUM args. exact (summary_istrncpy_sound SUM). Qed.

#[using="SEGS_wx SEGS_in_hull HULL_ok SP0_ok argH_high argH_agree SINV_frame SINV_agree"] Theorem node_x_sound_XPopFree :
  popfree_spec SEGS (x_popfree A) -> x_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0 XPopFree.
Proof. intros SUM args. exact (summary_popfree_sound SUM args). Qed.

End Sound.

End APSX.
