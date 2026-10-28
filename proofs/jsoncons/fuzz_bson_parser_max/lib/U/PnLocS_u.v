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
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u PnLocSIslandP_u PnLocSP_u Bs0_code_r7f81c_7f820_u Bs0_code_r7f8b8_7f8bc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMLOC.
Import PMS.

Lemma wseg_loc1 : wseg_ok RSEGS (Z_to_bv 64 821234) (Z.to_nat 1854) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_loc2 : wseg_ok RSEGS (Z_to_bv 64 824920) (Z.to_nat 88) = true. Proof. vm_compute. reflexivity. Qed.

Lemma cs_liA : forall k, In k PMK.cs_all -> In k PMLIP.KS_liA. Proof. PMCK.cs_all_tac. Qed.
Lemma cs_liB : forall k, In k PMK.cs_all -> In k PMLP.KS_liB. Proof. PMCK.cs_all_tac. Qed.
Lemma cs_liD : forall k, In k PMK.cs_all -> In k PMLP.KS_liD. Proof. PMCK.cs_all_tac. Qed.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Theorem locale_dtor_ok : PMS.locale_dtor_spec L.
Proof.
  unfold PMS.locale_dtor_spec, PMSP.locale_dtor_spec.
  intros fx R M model K o sp r Mh Ml K0 ENT A10 Hspo Hotop CELL KONT.
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. destruct STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
  LeanFeed.pfeed P (PMLP.liD_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [ PMK.sc | exact CELL ]).
  destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11).
  assert (EM : M1 = M).
  { apply FunctionalExtensionality.functional_extensionality. intros a. apply FR. }
  subst M1. unfold PMSP.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS|].
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M 0x81cd4 W_80694 r F_80694 ltac:(reflexivity) D_80694)|].
  - rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
  - exact RA1.
  - exact RA2.
  - apply (KONT fx1 R1). apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_liD. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma loc_true M : L5.u8_at RSEGS M 821744 1 -> L5.u64_at RSEGS M 821736 822784 -> PMST.loc_ok RSEGS AD M true.
Proof. intros G P. split; [exact G| exact P]. Qed.

Theorem locale_ctor_ok : PMS.locale_ctor_spec L HI.
Proof.
  unfold PMS.locale_ctor_spec, PMSP.locale_ctor_spec.
  intros fx R M model K LB cr o sp r b HH (Mh & Ml & Mm) K0 ENT A10 Hspo Hotop Ho8 DEFO BASE LOC KONT.
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
  pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
  assert (WRO : L5.writable RSEGS M o 8) by (apply (L5C.writable_of_defined RSEGS M o 8 DEFO); lia).
  pose proof (PMCK.lb_hi L HI HIok LB cr M _ HH) as LBhi.
  destruct BASE as (RO0 & (can & Hcan & CAN) & NL & LL).
  destruct b.
  - (* [comment removed for export] *)
    destruct LOC as (G & P0).
    LeanFeed.pfeed P (PMLP.liB_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [ PMK.sc | exact G | exact P0 ]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11 & CO).
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x81bdc R1 0x81c38 M1 (fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 8) K HH Mh Ml ltac:(lia) MS MG).
    { intros a Ha NP. apply FRZ; [exact Ha| |]; intros X; apply NP; [left|right]; exact X. }
    { intros a Ha. apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 2) a STK). lia. }
    { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x81c38 W_805f8 r F_805f8 ltac:(reflexivity) D_805f8)|].
    + rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
    + exact RA1.
    + exact RA2.
    + assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> ~ (o <= a < o + 8) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N1 N2. apply FRZ; [exact Ha| lia| lia]. }
      apply (KONT fx1 R1 M1).
      * apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_liB. exact Hk.
      * exact CO.
      * apply loc_true.
        -- apply (L5C.u8_at_agree RSEGS M M1); [|lia|lia|exact G]. intros i Hi. apply AG; lia.
        -- apply (L5C.u64_at_agree RSEGS M M1); [|lia|lia|exact P0]. intros i Hi. apply AG; lia.
      * apply PMK.hpres_of.
        -- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 2) [(o, 8)] M M1 (fun a => sp - 32 <= a < sp \/ o <= a < o + 8)).
           ++ intros a Ha NP. apply AG; [exact Ha| |]; intros X; apply NP; [left|right]; exact X.
           ++ exact STK.
           ++ exact LBhi.
           ++ intros a [X|X]; [left; lia| right; apply PMK.inW_here; exact X].
        -- apply (L5.defined_grows M M1 _ _ MG). exact SW.
        -- apply PMK.dk_grows. exact MG.
      * exact HH1.
  - (* [comment removed for export] *)
    cbn [PMST.loc_ok] in LOC. unfold PMST.img_clear_l in LOC.
    assert (C1 : L5.img_clear M 821234 823088) by (apply (LOC (0xc87f2, 0xc8f30)); cbn; auto).
    assert (C2 : L5.img_clear M 824920 825008) by (apply (LOC (0xc9658, 0xc96b0)); cbn; auto).
    cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in RO0, CAN, NL, LL.
    pose proof (PMCK.writable_img M 821234 1854 wseg_loc1 ltac:(lia) ltac:(lia) ltac:(lia)) as W1.
    pose proof (PMCK.writable_img M 824920 88 wseg_loc2 ltac:(lia) ltac:(lia) ltac:(lia)) as W2.
    LeanFeed.pfeed P (PMLIP.liA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => can | _ => 0 end)) ltac:(first [ PMK.sc | exact C1 | exact C2 | exact W1 | exact W2 | exact CAN ]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11 & CO & CG & CP).
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x81bdc R1 0x81c38 M1
             (fun a => (sp - 1024 <= a < sp - 1024 + 1024 \/ o + 0 <= a < o + 0 + 8) \/ (0 + 821234 <= a < 0 + 821234 + 1854 \/ 0 + 824920 <= a < 0 + 824920 + 88)) K HH Mh Ml ltac:(lia) MS MG).
    { intros a Ha NP. apply FRZ; [exact Ha| | | |]; intros X; apply NP; [left; left|left; right|right; left|right; right]; exact X. }
    { intros a [Ha|[Ha|Ha]].
      - apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 2) a STK). lia.
      - apply (PMKS.cwr_foot_S L LY LB (0xc87f2, 0xc8f30) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia].
      - apply (PMKS.cwr_foot_S L LY LB (0xc9658, 0xc96b0) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia]. }
    { intros a. apply PMK.or_dec; apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x81c38 W_805f8 r F_805f8 ltac:(reflexivity) D_805f8)|].
    + rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
    + exact RA1.
    + exact RA2.
    + apply (KONT fx1 R1 M1).
      * apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_liA. exact Hk.
      * exact CO.
      * apply loc_true; [exact CG| exact CP].
      * apply PMK.hpres_of.
        -- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 2) ((o, 8) :: PMSP.loc_W AD) M M1
                    (fun a => (sp - 1024 <= a < sp \/ o <= a < o + 8) \/ (821234 <= a < 823088 \/ 824920 <= a < 825008))).
           ++ intros a Ha NP. apply FRZ; [exact Ha| | | |]; intros X; apply NP; [left; left|left; right|right; left|right; right]; lia.
           ++ exact STK.
           ++ exact LBhi.
           ++ intros a [[X|X]|[X|X]]; [left; lia| right; apply PMK.inW_here; exact X | right | right ].
              ** apply PMK.inW_next. exists (821234, 1854). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
              ** apply PMK.inW_next. exists (824920, 88). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (L5.defined_grows M M1 _ _ MG). exact SW.
        -- apply PMK.dk_grows. exact MG.
      * exact HH1.
Qed.

End Stage.
End PMLOC.
