(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u PnSysSP_u Bs0_code_r59e7c_59e80_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSYS.
Import PMS.

Lemma wseg_sysg : wseg_ok RSEGS (Z_to_bv 64 821232) (Z.to_nat 2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cs_syA : forall k, In k PMK.cs_all -> In k PMSYP.KS_syA. Proof. PMCK.cs_all_tac. Qed.
Lemma cs_syB : forall k, In k PMK.cs_all -> In k PMSYP.KS_syB. Proof. PMCK.cs_all_tac. Qed.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Theorem syscat_ok : PMS.syscat_spec L HI.
Proof.
  unfold PMS.syscat_spec, PMSP.syscat_spec.
  intros fx R M model K LB cr sp r b HH (Mh & Ml & Mm) K0 ENT BASE SYS KONT.
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
  pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
  pose proof (PMCK.lb_hi L HI HIok LB cr M _ HH) as LBhi.
  destruct b; cbn [PMST.sys_ok pa_syscat_guard AD PnLayoutS_u.ADDR_S] in SYS.
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PMSYP.syA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [ PMK.sc | exact SYS ]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10).
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; intros a; apply FR).
    subst M1. unfold PMSP.cfg.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS|].
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M 0x5c298 W_5ac58 r F_5ac58 ltac:(reflexivity) D_5ac58)|].
    + rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
    + exact RA1.
    + exact RA2.
    + apply (KONT fx1 R1 M).
      * apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_syA. exact Hk.
      * rewrite L5K.rl10. exact B10.
      * exact SYS.
      * apply PMK.hpres_of; [apply PMK.ek_refl| exact SW| apply PMK.dk_refl].
      * exact HH.
  - (* [comment removed for export] *)
    pose proof (PMCK.writable_img M 821232 2 wseg_sysg ltac:(lia) ltac:(lia) ltac:(lia)) as W1.
    LeanFeed.pfeed P (PMSYP.syB_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [ PMK.sc | exact SYS | exact W1 ]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11 & B12 & G1 & G0).
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x5c280 R1 0x5c298 M1
             (fun a => sp - 16 <= a < sp - 16 + 16 \/ 0 + 821232 <= a < 0 + 821232 + 2) K HH Mh Ml ltac:(lia) MS MG).
    { intros a Ha NP. apply FRZ; [exact Ha| |]; intros X; apply NP; [left|right]; exact X. }
    { intros a [Ha|Ha].
      - apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia.
      - apply (PMKS.cwr_foot_S L LY LB (0xc87f0, 0xc87f2) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia]. }
    { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x5c298 W_5ac58 r F_5ac58 ltac:(reflexivity) D_5ac58)|].
    + rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
    + exact RA1.
    + exact RA2.
    + apply (KONT fx1 R1 M1).
      * apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_syB. exact Hk.
      * rewrite L5K.rl10. exact B10.
      * exact G0.
      * apply PMK.hpres_of.
        -- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 1) [(pa_syscat_guard AD, 2)] M M1 (fun a => sp - 16 <= a < sp \/ 821232 <= a < 821234)).
           ++ intros a Ha NP. apply FRZ; [exact Ha| |]; intros X; apply NP; [left|right]; lia.
           ++ exact STK.
           ++ exact LBhi.
           ++ intros a [X|X]; [left; lia| right; apply PMK.inW_here; cbn [pa_syscat_guard AD PnLayoutS_u.ADDR_S]; lia].
        -- apply (L5.defined_grows M M1 _ _ MG). exact SW.
        -- apply PMK.dk_grows. exact MG.
      * exact HH1.
Qed.

End Stage.
End PMSYS.
