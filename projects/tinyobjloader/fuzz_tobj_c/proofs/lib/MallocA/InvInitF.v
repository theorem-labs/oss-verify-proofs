(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "nat"; "list"; "bool"; "pair"; "None"; "false"; "fst"; "option"; "prod"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rl"; "rm"; "rw"; "obj_range"; "sobj"; "ss_objs"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pageZ"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "m_vm_lazy"; "page_in_ranges"; "vm_limit"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitF"; "band_out"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require KxA StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition band_out (rho : valuation) (o : sobj) : Prop := ltac2:(tb__ "0|1|
S6S7S17S0S0S1dVrho;Vo;A2M0A3S33A2S7S32S14S0S0G0A3A2A2").

Lemma obj_range_ext : ltac2:(tb__ "0|0|
S19S19S1eS1S2S21Q40A1S1cR3R1A2S1cR4R1A2A3Fi;S1S2SfS21Q8A1A1S1aR4R1A2S1aR5R1A2A3Fl;S2S16S0S0A2S1dR4R3A2S1dR5R3A2A3F_;F_;Fo;Frho';Frho;").
Proof.
  intros rho rho' o Hrw Hrl. unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite !(eval_ext_rwrl rho rho' _ Hrw Hrl). reflexivity.
Qed.

Lemma pageZ_u : ltac2:(tb__ "0|1|
S0SeS7Z0R2A2SbS8R3S9Z1000M0SaR2A1A2A2SdZ2Z40A2A2S2S0S22Q40S24R4R3A2A2S8R4S9G0SaR3A1A2A2A3F_;F_;Fk;Fq;").
Proof. intros q k H1 H2. unfold pageZ. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Theorem ensure_band_pages : ltac2:(tb__ "0|e|
S38S28SeS0S0S19SfS21Q40M0A1M1A1M2SfS2aA1M3S35S28S30S31S2fR9R7A2RaR5R4S11G3S26R3S27R2R1A2A4A6S2S0ScR7Z1000M4A2Z0A3S7S33R8A2S7S8R9S9G4SaRbA1A2A2S32A2SeS25R1RdA2S2S10S2cS24RcR2A2S2bRfA1A2S18A3F_;Fk;S0S3S7RcR1A2SbR1S8RcS9G4SaReA1A2M5A2A2A2S2S10S36S2eS29R10A1A1R2A2S13A3F_;Fz;S7S8RdG5A2S2dS29RfA1A1A2S34S1eS39RcA1S1fS37R11A1A1A3G1S20G1R1RdA3S3S7R10S22G0R2A2M6A2SbG6S8R10S9G4SaR12A1A2A2A2A2S0S3S7S22G0R4A2M7R1A2SbR1S8G7G4A2A2A2S5S2S15S21Q8A1M8A1M9S1bR12S23G0R2A2MaA2S12G8A1MbA3A1F_;Fz;F_;F_;Fp;S4S19S19S4G2G2S3S30S31S2fR14S8R12S9G4SaR13A1A2A2A2R15R2R1S11G3S26ReS27RdRcA2A4A6S3S1S2G1S1cR3R1A2S1cR11R1A2A3Fi;S3S1S2SfG8A1S1aR3R1A2S1aR11R1A2A3Fl;S3G1S5S3S7R12S22G0R1A2McA2SbGcS8R12S9G4SaR14A1A2A2MdA2A2A1S2G9S1bR4R2A2S1bR12R2A2A3F_;Fa;S3S0S3S7R12R1A2SbR1GdA2A2S5S2G9S1bR4GaA2GbA3A1F_;Fz;S3G1S20G1R1R10A3S20G1R2R3A3F_;Fp;G1S20G1R1R2A3S6S20G1R2R11A3S4SeSeS3S25R1R16A2S2G1R3S24R14R1A2A3A2Lk;A2A2F_;Fp;A2A2A2A2A2A2Ltp';A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fq;FBm;Fn;FMm;FA;").
Proof.
  intros A Mm n. induction n as [|n IH]; intros Bm q rho tp tr ms md Hsp Hqal Hqlo Hqhi Hlz Hacc Hlim Hobj Hdef.
  - exists rho, tp. rewrite Z.mul_0_r, Z.add_0_r. split; [exact Hsp|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|]. split; [intros z Hz; lia|]. split; [intros p Hp; exact Hp | intros p Hp; left; exact Hp].
  - rewrite Nat2Z.inj_succ in *.
    assert (BLO : 0x646000 <= SHADOW_BAND_LO) by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia).
    assert (BHI : SHADOW_BAND_HI < 2 ^ 63) by (unfold SHADOW_BAND_HI, HIGH_SHADOW_END; lia).
    destruct (IH Bm q rho tp tr ms md Hsp Hqal Hqlo ltac:(lia) ltac:(intros k Hk; apply Hlz; lia) ltac:(intros z Hz; apply Hacc; lia) ltac:(lia) Hobj
                ltac:(intros p Hp Hr; apply (Hdef p Hp); lia))
      as (rho1 & tp1 & Hsp1 & RW1 & RL1 & OUT1 & DEF1 & INC1 & ORG1).
    set (qn := q + 4096 * Z.of_nat n) in *.
    assert (Upn : bv_unsigned (pageZ q n) = qn) by (apply pageZ_u; lia).
    assert (UZ : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z).
    { intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
    pose proof Hsp1 as [Hsm1 (Htr1 & Hem1 & Hpaid1)]. cbn [w_tr w_cfg cfg_model fst snd] in Htr1, Hem1, Hpaid1.
    pose proof (erase_mat_eq_fields md Mm Hem1) as (Evm & Elz & _).
    destruct (page_mem (pageZ q n) tp1) eqn:Epm.
    +
      apply page_mem_In in Epm.
      exists rho1, tp1. split.
      { split; [exact Hsm1|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact Htr1|]. split; [exact Hem1 | lia]. }
      split; [exact RW1|]. split; [exact RL1|].
      split; [intros a Ha; apply OUT1; lia|].
      split.
      { intros z Hz. destruct (Z_lt_dec z qn) as [Hlt|Hge]; [apply DEF1; lia|].
        destruct (ORG1 _ Epm) as [Hin|(k & Hk & Ek)].
        - rewrite (OUT1 (Z_to_bv 64 z)) by (rewrite UZ by lia; lia). apply (Hdef _ Hin); rewrite ?Upn; lia.
        - exfalso. apply (f_equal bv_unsigned) in Ek. rewrite Upn, (pageZ_u q k) in Ek by lia. unfold qn in Ek. lia. }
      split; [exact INC1|].
      intros p Hp. destruct (ORG1 p Hp) as [H|(k & Hk & Ek)]; [left; exact H | right; exists k; split; [lia | exact Ek]].
    +
      apply page_mem_false in Epm.
      set (J' := fun (r : valuation) (_ : list word) (tr0 : list event) (md0 : Model) =>
                   KxA Mm (Bm + 4096 * Z.succ (Z.of_nat n)) r (pageZ qn 0 :: tp1) tr0 md0).
      assert (HJ' : forall r r' t t', J' r t tr md -> J' r' t' tr md) by (intros r r' t t' X; exact X).
      assert (EP0 : pageZ qn 0 = pageZ q n) by (unfold pageZ, qn; f_equal; lia).
      assert (PB : paid md (pageZ qn 0 :: tp1) <= Bm + 4096 * Z.succ (Z.of_nat n)).
      { pose proof (paid_cons_le md (pageZ qn 0) tp1) as X. unfold page_size in X. lia. }
      assert (Hsp0 : SPA segsA J' A rho1 tp1 (tr, mkCfg ms md)).
      { split; [exact Hsm1|]. subst J'. cbv beta. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact Htr1|]. split; [exact Hem1 | exact PB]. }
      destruct (SPA_prepay_pages_rm J' A qn 1 rho1 tp1 tr ms md Hsp0 HJ') as (rho2 & Hsp2 & RW2 & RL2 & Z2 & O2).
      * unfold qn. rewrite Z.add_mod, Hqal, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      * lia.
      * change (Z.of_nat 1) with 1. lia.
      * intros k Hk. replace k with 0%nat by lia. rewrite EP0, Elz. apply Hlz. lia.
      * intros k Hk. replace k with 0%nat by lia. rewrite EP0. exact Epm.
      * intros z Hz. change (Z.of_nat 1) with 1 in Hz. rewrite Evm. apply Hacc. lia.
      * unfold headroom. rewrite Evm. change (Z.of_nat 1) with 1. unfold page_size. lia.
      * apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hobj o Ho) as D. unfold band_out in D.
        rewrite (obj_range_ext rho rho1 o RW1 RL1). unfold ranges_disjoint. cbn [fst snd]. change (Z.of_nat 1) with 1. lia.
      * change (Z.of_nat 1) with 1 in *. cbn [pages_rev app] in Hsp2. rewrite Z.mul_1_r in *.
        exists rho2, (pageZ qn 0 :: tp1). split; [exact Hsp2|].
        split; [intros i; rewrite RW2; apply RW1|]. split; [intros l; rewrite RL2; apply RL1|].
        split; [intros a Ha; rewrite O2 by lia; apply OUT1; lia|].
        split.
        { intros z Hz. destruct (Z_lt_dec z qn) as [Hlt|Hge].
          - rewrite O2 by (rewrite UZ by lia; lia). apply DEF1. lia.
          - rewrite Z2 by lia. discriminate. }
        split; [intros p Hp; right; apply INC1; exact Hp|].
        intros p [<-|Hp]; [right; exists n; split; [lia | exact EP0]|].
        destruct (ORG1 p Hp) as [H|(k & Hk & Ek)]; [left; exact H | right; exists k; split; [lia | exact Ek]].
Qed.
