(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "ExitEv"; "m_fs"; "m_halted"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "False"; "@Corelib.Init.Datatypes"; "list"; "app"; "cons"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "reg_sv"; "sstate"; "valuation"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "ok_src"; "ok_tgt"; "etriple"; "tcons"; "triple"; "w_tr"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.X"; "K_tcons"; "ok_halted"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "exit_code"; "exited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "smatch_pending"; "ok_pframeJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "ok_frame"; "SP"; "SPJ"; "jpred"; "ok_frameJ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymComplete SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section X.
Variable segs : list Segment.

Definition K_tcons (Spec : list event -> Prop) (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0A1S1VK;R2R1A2S1bVSpec;R3A2F_;Fmd;Ftr;").

Lemma ok_frame_src_K : ltac2:(tb__ "0|1|
SaS0A1M0OF_;G0S1OF_;F_;S28R2R1A2S30Vsegs;S18Vsegs;R3A2R2A3F_;FK;FSpec;").
Proof using .
  intros Spec K HK tr ms md ms' Hk [Hh Hl] Hp Hs. split; [exact (HK _ _ Hk)|].
  cbn. intros [_ [[Hp' Hu] | [x8 [Hp' _]]]]; cbn in *; [|congruence].
  rewrite (mi_account_step_lazy_nil segs ms md Hl), Hs in Hu. discriminate.
Qed.

Lemma ok_frame_tgt_K : ltac2:(tb__ "0|1|
SaS0A1M0OF_;G0S1OF_;F_;S28R2R1A2S30Vsegs;S19Vsegs;R3A2R2A3F_;FK;FSpec;").
Proof using .
  intros Spec K HK tr ms md ms' Hk Hh Hp Hs. split; [exact (HK _ _ Hk)|].
  cbn. intros evs Hst.
  destruct (sstep_error_step segs ms md evs Hh Hp Hst); congruence.
Qed.

Lemma ok_pframe_src_K : ltac2:(tb__ "0|1|
SaS0A1M0OF_;G0S1OF_;F_;S28R2R1A2S2dVsegs;S18Vsegs;R3A2R2A3F_;FK;FSpec;").
Proof using . intros Spec K HK tr ms md x8 Hk Hp Hok. eapply ok_src_pending; eauto. Qed.

Lemma ok_pframe_tgt_K : ltac2:(tb__ "0|1|
SaS0A1M0OF_;G0S1OF_;F_;S28R2R1A2S2dVsegs;S19Vsegs;R3A2R2A3F_;FK;FSpec;").
Proof using . intros Spec K HK tr ms md x8 Hk Hp Hok. eapply ok_tgt_pending; eauto. Qed.

Definition ok_halted (ok : world -> Prop) (Spec : list event -> Prop) : Prop := ltac2:(tb__ "0|2|
SaS0A1M0S20S1S27Q40A1M1S1bVSpec;R4A2S5S10G1A1S4R3A1SfG1R2A2A3Vok;SeG0S21R6S22R5R4A2A4A1F_;F_;Fcode;Fmd;Fms;Ftr;").

Lemma ok_halted_src : ltac2:(tb__ "0|0|
SaS0A1OF_;S29S18Vsegs;R1A2R1A2FSpec;").
Proof using .
  intros Spec tr ms md code Ht Hh. split; [exact Ht|]. cbn.
  intros [Hnone _]. cbn in Hnone. congruence.
Qed.

Lemma ok_halted_tgt : ltac2:(tb__ "0|0|
SaS0A1OF_;S29S19Vsegs;R1A2R1A2FSpec;").
Proof using .
  intros Spec tr ms md code Ht Hh. split; [exact Ht|]. cbn.
  intros evs Hs. exact (halted_no_sstep Hh Hs).
Qed.

Lemma exit_code_lit : ltac2:(tb__ "0|2|
S15S14SaS0A1M0S20S1S23S2eVsegs;R6R5SeG0S21R4S22R3R2A2A4A4S5S12S13R6ZaA2S11R2A1A3S6S24Z0R3A2S25R3Z100A2A2S5S27Q40M1A1S2bR6A1S26G1R4A2A3F_;F_;F_;Fc;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md c Hsp H10 Hc.
  unfold exit_code.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0.
  change (10 + Z.of_nat 0) with 10 in G0. rewrite G0, H10. cbn [eval].
  apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite !Z.mod_small by lia.
  replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Definition exited_world (K : list event -> Model -> Prop) (S : sstate) (rho : valuation) : assn := ltac2:(tb__ "0|1|
S17S7SaS0A1M0G0S7S20S20S7S1S1S6VK;R3R1A2S6S2eVsegs;Vrho;VS;SeG0S21R3S22R2R1A2A4A4S5S17R4SeG0S21SbS0R3ScS0S2S2bR2A1S3R1A1A2SdS0A1A3A3S22R2S2cR2R1A2A2A4A3A2A2Lmd;A2Lms;A2Ltr;A2Lw';").

Lemma triple_exit : ltac2:(tb__ "0|2|
S17OF_;SaS0A1M0OF_;G0S1OF_;F_;S14S15S23S30Vsegs;R6R4A3S2dVsegs;R7R5A3S29R8R7A2S5S10S1eA1S2aVsegs;S16R6A1A2SfS1eS1fA2A3S8S5S12S13R7Z11A2M1S11Z5eA1A3S5S12G1S11Z5dA1A3A2S5S12S13R8ZaA2S11R6A1A3S6S24Z0R7A2S25R7Z100A2A2G0S1RdR2R1A2RfSbS0R3ScS0S2S26Q40RbA2S3R2A1A2SdS0A1A3A3A1F_;Fmd;Ftr;S1cVsegs;ReS31Vsegs;RcRbRaA4S17S9L_;A4F_;F_;F_;F_;F_;F_;F_;F_;Fc;Frho;FS;FK;FSpec;Fok;").
Proof using .
  intros ok Spec K S rho c Hokf Hokp Hokh Hi H17 H10 Hc Hspec.
  apply (@triple_seq segs ok _ (exited_world K S rho)).
  - apply triple1_triple. eapply triple1_ecall_det; [exact Hokf | exact Hi |].
    intros tr ms md Hsp Hk.
    pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
    pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
    assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
    { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
    split.
    + eapply Hokp; [exact Hk | exact Hp |]. apply exit_only_ok. exact Hno.
    + intros w' Hw. rewrite (wstep_exit_inv Hp (model_idle_halted Hh) Hno Hw).
      exists tr, ms, md. split; [exact Hk|]. split; [exact Hsp | reflexivity].
  - apply triple_halt. intros w' (tr & ms & md & Hk & Hsp & ->).
    split.
    + eapply Hokh; [|apply exited_halted].
      exists (tr ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (Hspec tr md Hk)|].
      rewrite (exit_code_lit rho S tr ms md c Hsp H10 Hc). apply is_prefix_refl.
    + intros w'' Hw'. exact (wstep_exited_none Hw').
Qed.

Lemma etriple_exit : ltac2:(tb__ "0|2|
SaS0A1M0S1OF_;F_;S14S15S23S5S10S1eA1S2aVsegs;S16R3A1A2SfS1eS1fA2A3S8S5S12S13R4Z11A2M1S11Z5eA1A3S5S12G1S11Z5dA1A3A2S5S12S13R5ZaA2S11R3A1A3S6S24Z0R4A2S25R4Z100A2A2S1aVsegs;S31Vsegs;R8R7R6A4S17S7G0G0S7S1S1S6RbR2R1A2S5G0S1dR3A1SbS0R2ScS0S2S26Q40R8A2S3R1A1A2SdS0A1A3A3A3A2Lmd;A2Ltr;A2Lw';A3F_;F_;F_;F_;Fc;Frho;FS;FK;").
Proof using .
  intros K S rho c Hi H17 H10 Hc.
  eapply etriple_ecall_det; [exact Hi|].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
  { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
  eexists. split; [exact (@wstep_exit_intro segs tr ms md _ Hp (model_idle_halted Hh) Hno)|].
  exists tr, md. split; [exact Hk|]. cbn. rewrite (exit_code_lit rho S tr ms md c Hsp H10 Hc). reflexivity.
Qed.

Definition exited_worldJ (J : jpred) (S : sstate) (rho : valuation) : assn := ltac2:(tb__ "0|1|
S17S7SaS0A1M0G0S7S20S20S7S1S1S6VJ;Vrho;R3R1A3S6S2eVsegs;Vrho;VS;SeG0S21R3S22R2R1A2A4A4S5S17R4SeG0S21SbS0R3ScS0S2S2bR2A1S3R1A1A2SdS0A1A3A3S22R2S2cR2R1A2A2A4A3A2A2Lmd;A2Lms;A2Ltr;A2Lw';").

Lemma triple_exitJ : ltac2:(tb__ "0|2|
S17OF_;SaS0A1M0OF_;S33S14S15S23S34Vsegs;R6R4A3S2fVsegs;R7R5A3S29R8R7A2S5S10S1eA1S2aVsegs;S16R6A1A2SfS1eS1fA2A3S8S5S12S13R7Z11A2M1S11Z5eA1A3S5S12G1S11Z5dA1A3A2S5S12S13R8ZaA2S11R6A1A3S6S24Z0R7A2S25R7Z100A2A2G0S1RdRbR2R1A3RfSbS0R3ScS0S2S26Q40RbA2S3R2A1A2SdS0A1A3A3A1F_;Fmd;Ftr;S1cVsegs;ReS32Vsegs;RcRbRaA4S17S9L_;A4F_;F_;F_;F_;F_;F_;F_;F_;Fc;Frho;FS;FJ;FSpec;Fok;").
Proof using .
  intros ok Spec J S rho c Hokf Hokp Hokh Hi H17 H10 Hc Hspec.
  apply (@triple_seq segs ok _ (exited_worldJ J S rho)).
  - apply triple1_triple. eapply triple1_ecall_detJ; [exact Hokf | exact Hi |].
    intros tr ms md Hsp Hk.
    pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
    pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
    assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
    { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
    split.
    + eapply Hokp; [exact Hk | exact Hp |]. apply exit_only_ok. exact Hno.
    + intros w' Hw. rewrite (wstep_exit_inv Hp (model_idle_halted Hh) Hno Hw).
      exists tr, ms, md. split; [exact Hk|]. split; [exact Hsp | reflexivity].
  - apply triple_halt. intros w' (tr & ms & md & Hk & Hsp & ->).
    split.
    + eapply Hokh; [|apply exited_halted].
      exists (tr ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (Hspec tr md Hk)|].
      rewrite (exit_code_lit rho S tr ms md c Hsp H10 Hc). apply is_prefix_refl.
    + intros w'' Hw'. exact (wstep_exited_none Hw').
Qed.

Lemma etriple_exitJ : ltac2:(tb__ "0|2|
S33S14S15S23S5S10S1eA1S2aVsegs;S16R3A1A2SfS1eS1fA2A3S8S5S12S13R4Z11A2M0S11Z5eA1A3S5S12G0S11Z5dA1A3A2S5S12S13R5ZaA2S11R3A1A3S6S24Z0R4A2S25R4Z100A2A2S1aVsegs;S32Vsegs;R8R7R6A4S17S7SaS0A1M1G1S7S1S1S6RbR9R2R1A3S5G1S1dR3A1SbS0R2ScS0S2S26Q40R8A2S3R1A1A2SdS0A1A3A3A3A2Lmd;A2Ltr;A2Lw';A3F_;F_;F_;F_;Fc;Frho;FS;FJ;").
Proof using .
  intros J S rho c Hi H17 H10 Hc.
  eapply etriple_ecall_detJ; [exact Hi|].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  assert (Hno : bv_unsigned (eval rho (reg_sv S 17)) = 93 \/ bv_unsigned (eval rho (reg_sv S 17)) = 94).
  { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
  eexists. split; [exact (@wstep_exit_intro segs tr ms md _ Hp (model_idle_halted Hh) Hno)|].
  exists tr, md. split; [exact Hk|]. cbn. rewrite (exit_code_lit rho S tr ms md c Hsp H10 Hc). reflexivity.
Qed.

End X.
