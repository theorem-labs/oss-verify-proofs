(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ExitSim PropExec CatSim CatExec SeqExec.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_StreamExec () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.delivered_writes"].


Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma write_to_mem_below : ltac2:(CDefT.buildp (gd_tbl_StreamExec ()) "Pdata,(0.(1.&8.))Pmem,P,(1.&40.)(2.(1.&8.))Pbuf,(1.&40.)Pa,(1.&40.)P,(3.(4.(5.&40.R2.)(6.(7.(1.&8.)R4.)))(8.+2.+40.))P,(9.(5.&40.R2.)(5.&40.R3.))(:.(2.(1.&8.))(;.R5.R4.R6.R3.)A1.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros data mem buf a Hnw Ha.
  rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_to_mem_above : ltac2:(CDefT.buildp (gd_tbl_StreamExec ()) "Pdata,(0.(1.&8.))Pmem,P,(1.&40.)(2.(1.&8.))Pbuf,(1.&40.)Pa,(1.&40.)P,(3.(4.(5.&40.R2.)(6.(7.(1.&8.)R4.)))(5.&40.R1.))(:.(2.(1.&8.))(;.R4.R3.R5.R2.)A1.R4.R2.)")
(* [comment removed for export] *).
Proof.
  intros data mem buf a Ha.
  rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_wtm_out : ltac2:(CDefT.buildp (gd_tbl_StreamExec ()) "Psegs,(0.$<.)Pdata,(0.(1.&8.))Pm,P,(1.&40.)(2.(1.&8.))Pbuf,(1.&40.)Pa,(1.&40.)Pn,$=.P,(3.(4.(5.&40.R2.)(6.R1.))(8.+2.+40.))P,(3.(4.(5.&40.R4.)(6.(7.(1.&8.)R6.)))(8.+2.+40.))P,(>.(3.(4.(5.&40.R5.)(6.(7.(1.&8.)R7.)))(5.&40.R4.))(3.(4.(5.&40.R4.)(6.R3.))(5.&40.R5.)))(:.(2.(0.(1.&8.)))(?.R9.(;.R7.R6.R8.)R5.R4.)(?.R9.R7.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
  intros x Hx. destruct Hd as [Hd | Hd].
  - apply write_to_mem_above. lia.
  - apply write_to_mem_below; [exact Hnb | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_write_to_mem : ltac2:(CDefT.buildp (gd_tbl_StreamExec ()) "Psegs,(0.$<.)Pdata,(0.(1.&8.))Pmem,P,(1.&40.)(2.(1.&8.))Pbuf,(1.&40.)P,(3.(4.(5.&40.R1.)(6.(7.(1.&8.)R3.)))(8.+2.+40.))(:.(2.(0.(1.&8.)))(?.R5.(;.R3.R2.R4.)R2.(7.(1.&8.)R4.))(10.(0.(1.&8.))R4.))")
(* [comment removed for export] *).
Proof.
  intros segs data mem buf Hnw.
  rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma adv_apply_write : ltac2:(CDefT.buildp (gd_tbl_StreamExec ()) "Pregs,(11.&5.(1.&40.))Ppc,(1.&40.)Psv,(2.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pret,(1.&40.)Pbuf,(1.&40.)Pdata,(0.(1.&8.))(:.$12.(13.(14.(15.R8.(16.Vfx,)R7.R6.(17.(1.&40.))(18.Vfx,)R5.R4.)(19.R3.(1:.(1;.(1.&40.)(0.(1.&8.)))(1<.(1.&40.)(0.(1.&8.))R2.R1.)(1=.(1;.(1.&40.)(0.(1.&8.)))))(1=.(1;.(1.&40.)(1.&40.)))(1=.(1;.(1.&40.)(1.&40.)))(1=.$1>.)(1=.(1;.(1.&40.)$=.)))))(1?.Vfx,(20.R8.(21.&5.+:.$22.)R3.)(23.R7.+4.)(;.R5.R2.R1.)R4.))")
(* [comment removed for export] *).
Proof.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_apply_delivered : ltac2:(CDefT.buildp (gd_tbl_StreamExec ()) "Pregs,(11.&5.(1.&40.))Ppc,(1.&40.)Psv,(2.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Prom,P,(1.&40.)(2.(1.&8.))Pret,(1.&40.)Pbuf,(1.&40.)Pdata,(0.(1.&8.))(:.$12.(13.(14.(15.R8.(16.Vfx,)R7.R6.(17.(1.&40.))(18.Vfx,)R5.R4.)(19.R3.(24.R2.R1.)(1=.(1;.(1.&40.)(1.&40.)))(1=.(1;.(1.&40.)(1.&40.)))(1=.$1>.)(1=.(1;.(1.&40.)$=.)))))(1?.Vfx,(20.R8.(21.&5.+:.$22.)R3.)(23.R7.+4.)(;.R5.R2.R1.)R4.))")
(* [comment removed for export] *).
Proof.
  intros regs pc sv mem rom ret buf data.
  destruct data as [|b rest]; [|apply adv_apply_write].
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes
       delivered_writes write_to_mem].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.
End WithFP1.
