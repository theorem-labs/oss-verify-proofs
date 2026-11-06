(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.RunsLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DFactsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLoopsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLeafU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SnWriteU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2BU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2CU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module VfPrintfU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLoopsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLeafU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SnWriteU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1.PcPass1U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2BU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2CU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S. Import NumLoopsU1.NDig.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition VF_RET_P1 : Z := 0xd85a0.
Definition VF_RET_P2 : Z := 0xd8640.
Definition VF_RET_SN : Z := 0xd8660.
Definition VF_RETPC : Z := 0xd86e0.

Section Vf.
  Context {fx : FPState}.
Context {RRND : RunRandom}.
  Variables (R : bvmap 5 word) (M : mem) (f ret v conv : Z).

  Hypothesis Hra : getr R 1%bv = Z_to_bv 64 ret.
  Hypothesis Hret : ret_ok (Z_to_bv 64 ret).
  Hypothesis Hretr : 0 <= ret < 2 ^ 64.
  Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 f.
  Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 f.
  Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 (f + 480).
  Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 (f + 352).
  Hypothesis Hflo : 2 ^ 32 <= f - 976.
  Hypothesis Hfhi : f + 484 < 2 ^ 47.
  Hypothesis Hal : f mod 16 = 0.
  Hypothesis HD : mdef M (f - 976) 1460.
  Hypothesis Fv : fld SEGS M (f + 352) 8 v.
  Hypothesis Hv : 0 <= v < 2 ^ 64.
  Hypothesis F0 : fld SEGS M (f + 480) 1 37.
  Hypothesis F1 : fld SEGS M (f + 481) 1 108.
  Hypothesis F2 : fld SEGS M (f + 482) 1 conv.
  Hypothesis F3 : fld SEGS M (f + 483) 1 0.
  Hypothesis Hconv : conv = 117 \/ conv = 100 \/ conv = 120.
  Hypothesis Gflags : fld SEGS M f 4 0.
  Hypothesis Gwrite : fld SEGS M (f + 72) 8 A_SN_WRITE.
  Hypothesis Gbuf : fld SEGS M (f + 88) 8 (f + 255).
  Hypothesis Gbsz : fld SEGS M (f + 96) 8 0.
  Hypothesis Gmode : fld SEGS M (f + 136) 4 0.
  Hypothesis Glock : fld SEGS M (f + 140) 4 (2 ^ 32 - 1).
  Hypothesis Glbf : fld SEGS M (f + 144) 4 (2 ^ 32 - 1).
  Hypothesis Gcookie : fld SEGS M (f + 152) 8 (f + 232).
  Hypothesis Gcs : fld SEGS M (f + 232) 8 (f + 456).
  Hypothesis Gcn : fld SEGS M (f + 240) 8 23.
  Hypothesis ROC : ro_clear Ly.L M.
  Hypothesis RRC : relro_clear M.
  Hypothesis FCAN : fld SEGS M A_CANARY 8 rr_canary.

  Definition vf_post (nc : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
    getr R' 10%bv = Z_to_bv 64 nc /\ 1 <= nc <= 21
    /\ (forall r, In r leaf_kept -> getr R' r = getr R r)
    /\ stores_in (fun a => zwin (f - 976) (f + 248) a \/ zwin (f + 456) (f + 456 + nc + 1) a) M M'.

  Lemma vfprintf_sn : exists nc R' M',
    msteps SEGS (@mkst fx R (Z_to_bv 64 A_VFPRINTF) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) /\ vf_post nc R' M'.
  Proof using fx RRND R M f ret v conv Hra Hret Hretr Hsp Ha0 Ha1 Ha2 Hflo Hfhi Hal HD Fv Hv F0 F1 F2 F3 Hconv Gflags Gwrite Gbuf Gbsz Gmode Glock Glbf Gcookie Gcs Gcn ROC RRC FCAN.
    set (E := Eseed R [Z_to_bv 64 rr_canary]).
    assert (HR : regs_ok E (srs sr_id [(10%bv : reg, EVar 2); (11%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 480)); (12%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 352))]) R).
    { srs_ok. }
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-976)) (ELit 1460); KRange (EVar 2) (2 ^ 32 + 976) (2 ^ 47 - 484); KAlign (EVar 2) 16;
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000; KWord (SA (ELit 0) A_CANARY) (N.to_nat 8) (EVar 32)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ f (-976) 1460); [evs; exact Hsp | lia | lia | lia | lia | exact HD].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal].
      - apply kimg_ro. exact ROC. - apply kimg_relro. exact RRC. - unfold A_CANARY in *. (pose proof rr_canary_range; kwa FCAN). }
    xrun_at HR HK fx A_VFPRINTF (seg_rom SEGS) 100%nat [A_PRINTF_CORE; A_SN_WRITE; VF_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1. wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
    assert (ST1 : stores_in (zwin (f - 368) f) M M1) by (subst M1; stores_tower).
    assert (SV1 : slots SEGS M1 f [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv]) by (subst M1; slots_tower).
    assert (Gcan1 : fld SEGS M1 (f - 64) 8 rr_canary) by (unfold fld; subst M1; peel).
    assert (Gap1 : fld SEGS M1 (f - 368) 8 (f + 352)) by (unfold fld; subst M1; peel).
    assert (HD1 : mdef M1 (f - 976) 1460) by (eapply stores_in_mdef; [exact ST1 | exact HD]).
    assert (T01 : forall a (n : nat) x, (a + Z.of_nat n <= f - 368 \/ f <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M1 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    pose proof (T01 (f + 480) 1%nat 37 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F0) as F0'.
    pose proof (T01 (f + 481) 1%nat 108 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F1) as F1'.
    pose proof (T01 (f + 482) 1%nat conv ltac:(lia) ltac:(lia) ltac:(cbn; lia) F2) as F2'.
    pose proof (T01 (f + 483) 1%nat 0 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F3) as F3'.
    replace (f + 481) with (f + 480 + 1) in F1' by lia. replace (f + 482) with (f + 480 + 2) in F2' by lia. replace (f + 483) with (f + 480 + 3) in F3' by lia.
    regval HR1 (1%bv : reg) VF_RET_P1 X1. regval HR1 (2%bv : reg) (f - 368) X2. regval HR1 (10%bv : reg) 0 X10. regval HR1 (11%bv : reg) (f + 480) X11.

    destruct (pcore_pass1 R1 M1 (f - 368) VF_RET_P1 (f + 480) conv X1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold VF_RET_P1; lia)
                X2 X10 X11 ltac:(lia) ltac:(lia) ltac:(mlia)
                ltac:(eapply mdef_sub; [exact HD1 | lia | lia]) ltac:(lia) ltac:(lia) ltac:(lia)
                F0' F1' F2' F3' Hconv
                ltac:(eapply ro_clear_hi; [exact ROC | exact ST1 | intros a Ha; unfold zwin in Ha; lia])
                ltac:(eapply relro_clear_hi; [exact RRC | exact ST1 | intros a Ha; unfold zwin in Ha; lia])
                ltac:(eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; unfold zwin, A_CANARY in *; lia | unfold A_CANARY; lia | unfold A_CANARY; cbn; lia | exact FCAN]))
      as (R2 & M2 & Hms2 & Y10 & YK2 & ST2).
    assert (ST02 : stores_in (zwin (f - 912) f) M M2).
    { eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact ST2 | ..]; intros a Ha; unfold zwin in *; lia. }
    assert (T02 : forall a (n : nat) x, (a + Z.of_nat n <= f - 912 \/ f <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST02 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    assert (T12 : forall a (n : nat) x, (a + Z.of_nat n <= f - 912 \/ f - 368 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M1 a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST2 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }

    assert (Z2 : getr R2 2%bv = Z_to_bv 64 (f - 368)) by (rewrite (YK2 2%bv) by inl; exact X2).
    assert (Z8 : getr R2 8%bv = Z_to_bv 64 f) by (rewrite (YK2 8%bv) by inl; regval HR1 (8%bv : reg) f X; exact X).
    assert (Z9 : getr R2 9%bv = Z_to_bv 64 (f + 480)) by (rewrite (YK2 9%bv) by inl; regval HR1 (9%bv : reg) (f + 480) X; exact X).
    pose proof (T02 (f + 140) 4%nat (2 ^ 32 - 1) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Glock) as Glock2.
    pose proof (T02 f 4%nat 0 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Gflags) as Gflags2.
    pose proof (T02 (f + 96) 8%nat 0 ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gbsz) as Gbsz2.
    pose proof (T02 (f + 88) 8%nat (f + 255) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gbuf) as Gbuf2.
    pose proof (T02 (f + 136) 4%nat 0 ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gmode) as Gmode2.
    set (E2 := Eseed R2 []).
    assert (HR2 : regs_ok E2 (srs sr_id [(2%bv : reg, EAlu ALU_ADD (EVar 8) (ELit (-368))); (9%bv : reg, EAlu ALU_ADD (EVar 8) (ELit 480))]) R2).
    { srs_ok. }
    assert (HK2 : know_ok SEGS E2 M2
      [KWr (SA (EVar 8) (-976)) (ELit 1460); KRange (EVar 8) (2 ^ 32 + 976) (2 ^ 47 - 484); KAlign (EVar 8) 16; KRange (EVar 10) 0 0;
       KWord (SA (EVar 8) 140) (N.to_nat 4) (ELit (2 ^ 32 - 1)); KWord (SA (EVar 8) 0) (N.to_nat 4) (ELit 0);
       KWord (SA (EVar 8) 96) (N.to_nat 8) (ELit 0); KWord (SA (EVar 8) 88) (N.to_nat 8) (EAlu ALU_ADD (EVar 8) (ELit 255));
       KWord (SA (EVar 8) 136) (N.to_nat 4) (ELit 0);
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ f (-976) 1460); [evs; exact Z8 | lia | lia | lia | lia | eapply stores_in_mdef; [exact ST02 | exact HD]].
      - krv Z8. - eapply kalign_var; [evs; exact Z8 | lia | lia | exact Hal]. - krv Y10.
      - kwv Glock2 Z8. - kwv Gflags2 Z8. - kwv Gbsz2 Z8. - kwe Gbuf2 Z8. - kwv Gmode2 Z8.
      - apply kimg_ro. eapply ro_clear_hi; [exact ROC | exact ST02 | intros a Ha; unfold zwin in Ha; lia].
      - apply kimg_relro. eapply relro_clear_hi; [exact RRC | exact ST02 | intros a Ha; unfold zwin in Ha; lia]. }
    xrun_at HR2 HK2 fx VF_RET_P1 (seg_rom SEGS) 100%nat [A_PRINTF_CORE; A_SN_WRITE; VF_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK2. rename R' into R3. rename HR' into HR3. rename Hms into Hms3. wnorm_in Hms3.
    lazymatch type of Hms3 with msteps _ _ (mkst _ _ ?mm _) => set (M3 := mm) in Hms3 end.
    assert (ST3 : stores_in (zwin f (f + 144)) M2 M3) by (subst M3; stores_tower).
    assert (ST03 : stores_in (fun a => zwin (f - 912) f a \/ zwin f (f + 144) a) M M3).
    { eapply (stores_in_join _ _ _ M M2 M3); [exact ST02 | exact ST3 | ..]; intros a Ha; unfold zwin in *; lia. }
    assert (HD3 : mdef M3 (f - 368 - 608) 1460) by (replace (f - 368 - 608) with (f - 976) by lia; eapply stores_in_mdef; [exact ST03 | exact HD]).
    assert (T03 : forall a (n : nat) x, (a + Z.of_nat n <= f - 912 \/ f + 144 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M3 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST03 | intros y Hy; cbv beta; unfold zwin; lia | lia | lia | exact HF]. }
    assert (T23 : forall a (n : nat) x, (a + Z.of_nat n <= f \/ f + 144 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M2 a n x -> fld SEGS M3 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST3 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    pose proof (T23 (f - 368) 8%nat (f + 352) ltac:(lia) ltac:(lia) ltac:(cbn; lia) (T12 (f - 368) 8%nat (f + 352) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gap1)) as Fap3.
    pose proof (T03 (f + 352) 8%nat v ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Fv) as Fv3.
    pose proof (T03 (f + 480) 1%nat 37 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F0) as F03. replace (f + 480) with (f - 368 + 848) in F03 by lia.
    pose proof (T03 (f + 481) 1%nat 108 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F1) as F13. replace (f + 481) with (f - 368 + 849) in F13 by lia.
    pose proof (T03 (f + 482) 1%nat conv ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F2) as F23. replace (f + 482) with (f - 368 + 850) in F23 by lia.
    pose proof (T03 (f + 483) 1%nat 0 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F3) as F33. replace (f + 483) with (f - 368 + 851) in F33 by lia.
    pose proof (T03 (f + 144) 4%nat (2 ^ 32 - 1) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Glbf) as Flbf3. replace (f + 144) with (f - 368 + 368 + 144) in Flbf3 by lia.
    assert (Fflags3 : fld SEGS M3 (f - 368 + 368) 4 0) by (replace (f - 368 + 368) with f by lia; unfold fld; subst M3; peel).
    assert (Fwend3 : fld SEGS M3 (f - 368 + 368 + 32) 8 (f - 368 + 96)) by (replace (f - 368 + 368 + 32) with (f + 32) by lia; unfold fld; subst M3; peel).
    assert (Fwpos3 : fld SEGS M3 (f - 368 + 368 + 40) 8 (f - 368 + 16)) by (replace (f - 368 + 368 + 40) with (f + 40) by lia; unfold fld; subst M3; peel).
    replace (f + 352) with (f - 368 + 720) in Fap3, Fv3 by lia.
    assert (ROC3 : ro_clear Ly.L M3) by (eapply ro_clear_hi; [exact ROC | exact ST03 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia]).
    assert (RRC3 : relro_clear M3) by (eapply relro_clear_hi; [exact RRC | exact ST03 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia]).
    assert (FCAN3 : fld SEGS M3 A_CANARY 8 rr_canary) by (eapply (fld_via_stores SEGS); [exact ST03 | intros y Hy; cbv beta; unfold zwin, A_CANARY in *; lia | unfold A_CANARY; lia | unfold A_CANARY; cbn; lia | exact FCAN]).
    regval HR3 (1%bv : reg) VF_RET_P2 Y1. regval HR3 (2%bv : reg) (f - 368) Y2. regval HR3 (10%bv : reg) (f - 368 + 368) Y10'.
    regval HR3 (11%bv : reg) (f - 368 + 848) Y11. regval HR3 (12%bv : reg) (f - 368) Y12. regval HR3 (13%bv : reg) (f - 368 + 96) Y13. regval HR3 (14%bv : reg) (f - 368 + 264) Y14.
    pose proof (@PcPass2CU1.pcore_pass2 fx RRND R3 M3 (f - 368) VF_RET_P2 v conv Y1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold VF_RET_P2; lia) Y2 Y10' Y11 Y12 Y13 Y14
                  ltac:(lia) ltac:(lia) ltac:(mlia) HD3 Fap3 Fv3 Hv F03 F13 F23 F33 Hconv Fflags3 Fwend3 Fwpos3 Flbf3 ROC3 RRC3 FCAN3) as LP.
    destruct LP as (nc & R4 & M4 & Hms4 & P10 & Pnc & PK & PST & Pwpos).

    assert (ST04 : stores_in (fun a => zwin (f - 976) (f + 144) a) M M4).
    { eapply (stores_in_join _ _ _ M M3 M4); [exact ST03 | exact PST | ..]; intros a Ha; cbv beta in Ha; unfold zwin in *; lia. }
    assert (T34 : forall a (n : nat) x, (a + Z.of_nat n <= f - 976 \/ f - 272 <= a) -> (a + Z.of_nat n <= f + 40 \/ f + 48 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M3 a n x -> fld SEGS M4 a n x).
    { intros a n x G1 G2 G3 G4 HF. eapply (fld_via_stores SEGS); [exact PST | intros y Hy; cbv beta; unfold zwin; lia | lia | lia | exact HF]. }
    assert (T04 : forall a (n : nat) x, (a + Z.of_nat n <= f - 976 \/ f + 144 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M4 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST04 | intros y Hy; cbv beta; unfold zwin; lia | lia | lia | exact HF]. }
    assert (W2 : getr R4 2%bv = Z_to_bv 64 (f - 368)) by (rewrite (PK 2%bv) by inl; exact Y2).
    assert (W8 : getr R4 8%bv = Z_to_bv 64 f) by (rewrite (PK 8%bv) by inl; rewrite (syms_id_sound R2 _ _ R3 [8%bv] HR3 eq_refl 8%bv ltac:(inl)); exact Z8).
    assert (W20 : getr R4 20%bv = Z_to_bv 64 (f + 255)) by (rewrite (PK 20%bv) by inl; regval HR3 (20%bv : reg) (f + 255) X; exact X).
    assert (W19 : getr R4 19%bv = Z_to_bv 64 1) by (rewrite (PK 19%bv) by inl; regval HR3 (19%bv : reg) 1 X; exact X).
    assert (W21 : getr R4 21%bv = Z_to_bv 64 0) by (rewrite (PK 21%bv) by inl; regval HR3 (21%bv : reg) 0 X; exact X).
    pose proof (T02 (f + 72) 8%nat A_SN_WRITE ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gwrite) as Gwrite2.
    assert (Gwrite3 : fld SEGS M3 (f + 72) 8 A_SN_WRITE) by (unfold fld in Gwrite2 |- *; subst M3; peel; exact Gwrite2).
    pose proof (T34 (f + 72) 8%nat A_SN_WRITE ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Gwrite3) as Gwrite4.
    set (E4 := Eseed R4 [Z_to_bv 64 nc]).
    assert (HR4 : regs_ok E4 (srs sr_id [(2%bv : reg, EAlu ALU_ADD (EVar 8) (ELit (-368)))]) R4) by srs_ok.
    assert (HK4 : know_ok SEGS E4 M4
      [KRange (EVar 8) (2 ^ 32 + 976) (2 ^ 47 - 484); KRange (EVar 20) (2 ^ 32) (2 ^ 47); KRange (EVar 19) 1 1;
       KWord (SA (EVar 8) 72) (N.to_nat 8) (ELit A_SN_WRITE); KImg 0x10000 0xe8000; KImg 0xe8000 0xef000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - krv W8. - krv W20. - krv W19. - unfold A_SN_WRITE in *; kwv Gwrite4 W8.
      - apply kimg_ro. eapply ro_clear_hi; [exact ROC | exact ST04 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia].
      - apply kimg_relro. eapply relro_clear_hi; [exact RRC | exact ST04 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia]. }
    xrun_at HR4 HK4 fx VF_RET_P2 (seg_rom SEGS) 100%nat [A_PRINTF_CORE; A_SN_WRITE; VF_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK4. rename R' into R5. rename HR' into HR5. rename Hms into Hms5.
    regval HR5 (1%bv : reg) VF_RET_SN U1. regval HR5 (2%bv : reg) (f - 368) U2. regval HR5 (10%bv : reg) f U10. regval HR5 (12%bv : reg) 0 U12.
    assert (HD4 : mdef M4 (f - 976) 1460) by (eapply stores_in_mdef; [exact ST04 | exact HD]).
    pose proof (T04 (f + 152) 8%nat (f + 232) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gcookie) as Gcookie4.
    pose proof (T04 (f + 232) 8%nat (f + 456) ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gcs) as Gcs4.
    pose proof (T04 (f + 240) 8%nat 23 ltac:(lia) ltac:(lia) ltac:(cbn; lia) Gcn) as Gcn4. replace (f + 240) with (f + 232 + 8) in Gcn4 by lia.
    assert (G56_3 : fld SEGS M3 (f + 56) 8 (f - 352)) by (unfold fld; subst M3; peel).
    assert (G88_3 : fld SEGS M3 (f + 88) 8 (f - 352)) by (unfold fld; subst M3; peel).
    pose proof (T34 (f + 56) 8%nat (f - 352) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) G56_3) as G56_4.
    pose proof (T34 (f + 88) 8%nat (f - 352) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) G88_3) as G88_4.
    pose proof Pwpos as G40_4. replace (f - 368 + 368 + 40) with (f + 40) in G40_4 by lia. replace (f - 368 + 16 + nc) with (f - 352 + nc) in G40_4 by lia.
    destruct (mdef_rdn SEGS M4 (f - 976) 1460 624 (Z.to_nat nc) HD4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (bsw & RDw & Hlenw).
    replace (f - 976 + 624) with (f - 352) in RDw by lia.
    pose proof (@sn_write0 fx R5 M4 (f - 368) VF_RET_SN f (f + 232) (f + 456) 23 nc (f - 352) (f - 352) bsw) as LS.
    repeat lazymatch type of LS with (exists _, _) => fail | forall _ : ?T, _ =>
      specialize (LS ltac:(first [eassumption | lia | apply bv_eq; vm_compute; reflexivity | unfold VF_RET_SN; lia | mlia
                                  | eapply mdef_sub; [exact HD4 | lia | lia] ])) end.
    match type of LS with ?t => idtac t end.
    destruct LS as (R6 & M6 & Hms6 & Q10 & QK & ST6 & Qc0 & Qc8 & Q40 & Q56 & Qnul & Q152 & Q88).

    assert (ST06 : stores_in (fun a => zwin (f - 976) (f + 144) a \/ zwin (f + 456) (f + 456 + nc + 1) a \/ zwin (f + 232) (f + 248) a) M M6).
    { eapply (stores_in_join _ _ _ M M4 M6); [exact ST04 | exact ST6 | ..]; intros a Ha; cbv beta in Ha; cbv beta; unfold zwin in *; lia. }
    assert (T46 : forall a (n : nat) x, (a + Z.of_nat n <= f - 432 \/ f - 368 <= a) -> (a + Z.of_nat n <= f + 40 \/ f + 48 <= a) -> (a + Z.of_nat n <= f + 56 \/ f + 64 <= a) ->
                 (a + Z.of_nat n <= f + 232 \/ f + 248 <= a) -> a + Z.of_nat n <= f + 456 -> 0 <= a -> fld SEGS M4 a n x -> fld SEGS M6 a n x).
    { intros a n x G1 G2 G3 G4 G5 G6 HF. eapply (fld_via_stores SEGS); [exact ST6 | intros y Hy; cbv beta; unfold zwin; lia | lia | lia | exact HF]. }
    assert (Gfl6 : fld SEGS M6 f 4 0).
    { apply T46; [cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | lia |]. apply T34; [cbn; lia | cbn; lia | lia | cbn; lia |]. replace (f - 368 + 368) with f in Fflags3 by lia. exact Fflags3. }
    assert (Gcan6 : fld SEGS M6 (f - 64) 8 rr_canary).
    { apply T46; [cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia | lia |]. apply T34; [cbn; lia | cbn; lia | lia | cbn; lia |].
      apply T23; [cbn; lia | lia | cbn; lia |]. apply T12; [cbn; lia | lia | cbn; lia | exact Gcan1]. }
    assert (FCAN6 : fld SEGS M6 A_CANARY 8 rr_canary).
    { eapply (fld_via_stores SEGS); [exact ST06 | intros y Hy; cbv beta; unfold zwin, A_CANARY in *; lia | unfold A_CANARY; lia | unfold A_CANARY; cbn; lia | exact FCAN]. }
    assert (SV6 : slots SEGS M6 f [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv]).
    { eapply slots_agree; [exact SV1 | cbn; lia | lia |]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul].
      assert (A12 : agree_on (zwin (f - 56) f) M1 M2) by (eapply stores_in_agree; [exact ST2 | intros b Hb; unfold zwin in *; lia]).
      assert (A23 : agree_on (zwin (f - 56) f) M2 M3) by (eapply stores_in_agree; [exact ST3 | intros b Hb; unfold zwin in *; lia]).
      assert (A34 : agree_on (zwin (f - 56) f) M3 M4) by (eapply stores_in_agree; [exact PST | intros b Hb; cbv beta; unfold zwin in *; lia]).
      assert (A46 : agree_on (zwin (f - 56) f) M4 M6) by (eapply stores_in_agree; [exact ST6 | intros b Hb; cbv beta; unfold zwin in *; lia]).
      intros b Hb. rewrite (A46 b Hb), (A34 b Hb), (A23 b Hb). exact (A12 b Hb). }
    assert (V2' : getr R6 2%bv = Z_to_bv 64 (f - 368)) by (rewrite (QK 2%bv) by inl; exact U2).
    assert (V8 : getr R6 8%bv = Z_to_bv 64 f) by (rewrite (QK 8%bv) by inl; regval HR5 (8%bv : reg) f X; exact X).
    assert (V9 : getr R6 9%bv = Z_to_bv 64 nc) by (rewrite (QK 9%bv) by inl; regval HR5 (9%bv : reg) nc X; exact X).
    assert (V18 : getr R6 18%bv = Z_to_bv 64 A_CANARY) by (rewrite (QK 18%bv) by inl; rewrite (syms_id_sound R4 _ _ R5 [18%bv] HR5 eq_refl 18%bv ltac:(inl)); rewrite (PK 18%bv) by inl;
                                                           rewrite (syms_id_sound R2 _ _ R3 [18%bv] HR3 eq_refl 18%bv ltac:(inl)); rewrite (YK2 18%bv) by inl; regval HR1 (18%bv : reg) A_CANARY X; exact X).
    assert (V19 : getr R6 19%bv = Z_to_bv 64 1) by (rewrite (QK 19%bv) by inl; regval HR5 (19%bv : reg) 1 X; exact X).
    assert (V20 : getr R6 20%bv = Z_to_bv 64 (f + 255)) by (rewrite (QK 20%bv) by inl; regval HR5 (20%bv : reg) (f + 255) X; exact X).
    assert (V21 : getr R6 21%bv = Z_to_bv 64 0) by (rewrite (QK 21%bv) by inl; regval HR5 (21%bv : reg) 0 X; exact X).
    set (E6 := Eseed R6 [Z_to_bv 64 nc; Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv; Z_to_bv 64 rr_canary]).
    assert (HR6 : regs_ok E6 (srs sr_id [(2%bv : reg, EAlu ALU_ADD (EVar 8) (ELit (-368))); (20%bv : reg, EAlu ALU_ADD (EVar 8) (ELit 255))]) R6) by srs_ok.
    assert (HK6 : know_ok SEGS E6 M6
      [KWr (SA (EVar 8) (-976)) (ELit 1460); KRange (EVar 8) (2 ^ 32 + 976) (2 ^ 47 - 484); KAlign (EVar 8) 16;
       KRange (EVar 9) 1 21; KRange (EVar 18) A_CANARY A_CANARY; KRange (EVar 19) 1 1; KRange (EVar 21) 0 0;
       KWord (SA (EVar 8) 40) (N.to_nat 8) (EAlu ALU_ADD (EVar 8) (ELit (-352))); KWord (SA (EVar 8) 0) (N.to_nat 4) (ELit 0);
       KWord (SA (EVar 8) (-64)) (N.to_nat 8) (EVar 40); KWord (SA (ELit 0) A_CANARY) (N.to_nat 8) (EVar 40);
       KWord (SA (EVar 8) (-8)) (N.to_nat 8) (EVar 33); KWord (SA (EVar 8) (-16)) (N.to_nat 8) (EVar 34); KWord (SA (EVar 8) (-24)) (N.to_nat 8) (EVar 35);
       KWord (SA (EVar 8) (-32)) (N.to_nat 8) (EVar 36); KWord (SA (EVar 8) (-40)) (N.to_nat 8) (EVar 37); KWord (SA (EVar 8) (-48)) (N.to_nat 8) (EVar 38);
       KWord (SA (EVar 8) (-56)) (N.to_nat 8) (EVar 39);
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ f (-976) 1460); [evs; exact V8 | lia | lia | lia | lia | eapply stores_in_mdef; [exact ST06 | exact HD]].
      - krv V8. - eapply kalign_var; [evs; exact V8 | lia | lia | exact Hal].
      - krv V9. - unfold A_CANARY in *; krv V18. - krv V19. - krv V21.
      - kwz Q40 V8. - kwv Gfl6 V8. - (pose proof rr_canary_range; kwv Gcan6 V8). - unfold A_CANARY in *; (pose proof rr_canary_range; kwa FCAN6).
      - kwe (SV6 0%nat ltac:(cbn [length]; lia)) V8. - kwe (SV6 1%nat ltac:(cbn [length]; lia)) V8. - kwe (SV6 2%nat ltac:(cbn [length]; lia)) V8.
      - kwe (SV6 3%nat ltac:(cbn [length]; lia)) V8. - kwe (SV6 4%nat ltac:(cbn [length]; lia)) V8. - kwe (SV6 5%nat ltac:(cbn [length]; lia)) V8.
      - kwe (SV6 6%nat ltac:(cbn [length]; lia)) V8.
      - apply kimg_ro. eapply ro_clear_hi; [exact ROC | exact ST06 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia].
      - apply kimg_relro. eapply relro_clear_hi; [exact RRC | exact ST06 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia]. }
    xrun_at HR6 HK6 fx VF_RET_SN (seg_rom SEGS) 100%nat [A_PRINTF_CORE; A_SN_WRITE; VF_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK6. rename Hms into Hms7. wnorm_in Hms7.
    lazymatch type of Hms7 with msteps _ _ (mkst _ _ ?mm _) => set (M7 := mm) in Hms7 end.
    assert (ST7 : stores_in (zwin f (f + 104)) M6 M7) by (subst M7; stores_tower).
    regval HR' (1%bv : reg) ret T1. regval HR' (10%bv : reg) nc T10.
    pose proof (ret_at SEGS VF_RETPC R' M7 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) T1 Hret) as Hms8.
    exists nc, R', M7. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
      eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|]. eapply msteps_trans; [exact Hms6|].
      eapply msteps_trans; [exact Hms7 | exact Hms8]. }
    split; [exact T10|]. split; [exact Pnc|]. split.
    { intros r Hr. unfold leaf_kept in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR' QK HR5 PK HR3 YK2 HR1|]). destruct Hr. }
    eapply (stores_in_join _ _ _ M M6 M7); [exact ST06 | exact ST7 | ..]; intros a Ha; cbv beta in Ha; cbv beta; unfold zwin in *; lia.
  Qed.
End Vf.
End VfPrintfU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemset.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module VsnPrintfU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemset.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DFactsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLoopsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLeafU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SnWriteU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1.PcPass1U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2BU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2CU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DoPutDefsU1.VfPrintfU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S. Import NumLoopsU1.NDig.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition VSN_RET_MS : Z := 0xdcec0.
Definition VSN_RET_VF : Z := 0xdcefc.
Definition VSN_RETPC : Z := 0xdcf20.

Section Vsn.
  Context {fx : FPState}.
Context {RRND : RunRandom}.
  Variables (R : bvmap 5 word) (M : mem) (s ret v conv : Z).

  Hypothesis Hra : getr R 1%bv = Z_to_bv 64 ret.
  Hypothesis Hret : ret_ok (Z_to_bv 64 ret).
  Hypothesis Hretr : 0 <= ret < 2 ^ 64.
  Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 s.
  Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 (s + 152).
  Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 24.
  Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 (s + 176).
  Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 (s + 48).
  Hypothesis Hslo : 2 ^ 32 <= s - 1280.
  Hypothesis Hshi : s + 180 < 2 ^ 47.
  Hypothesis Hal : s mod 16 = 0.
  Hypothesis HD : mdef M (s - 1280) 1460.
  Hypothesis Fv : fld SEGS M (s + 48) 8 v.
  Hypothesis Hv : 0 <= v < 2 ^ 64.
  Hypothesis F0 : fld SEGS M (s + 176) 1 37.
  Hypothesis F1 : fld SEGS M (s + 177) 1 108.
  Hypothesis F2 : fld SEGS M (s + 178) 1 conv.
  Hypothesis F3 : fld SEGS M (s + 179) 1 0.
  Hypothesis Hconv : conv = 117 \/ conv = 100 \/ conv = 120.
  Hypothesis ROC : ro_clear Ly.L M.
  Hypothesis RRC : relro_clear M.
  Hypothesis FCAN : fld SEGS M A_CANARY 8 rr_canary.

  Definition vsn_post (nc : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
    getr R' 10%bv = Z_to_bv 64 nc /\ 1 <= nc <= 21
    /\ (forall r, In r leaf_kept -> getr R' r = getr R r)
    /\ stores_in (fun a => zwin (s - 1280) s a \/ zwin (s + 152) (s + 152 + nc + 1) a) M M'.

  Lemma vsnprintf24 : exists nc R' M',
    msteps SEGS (@mkst fx R (Z_to_bv 64 A_VSNPRINTF) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) /\ vsn_post nc R' M'.
  Proof using fx RRND R M s ret v conv Hra Hret Hretr Hsp Ha0 Ha1 Ha2 Ha3 Hslo Hshi Hal HD Fv Hv F0 F1 F2 F3 Hconv ROC RRC FCAN.
    set (E := Eseed R [Z_to_bv 64 rr_canary]).
    assert (HR : regs_ok E (srs sr_id [(10%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 152)); (12%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 176)); (13%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 48))]) R) by srs_ok.
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-1280)) (ELit 1460); KRange (EVar 2) (2 ^ 32 + 1280) (2 ^ 47 - 180); KAlign (EVar 2) 16; KRange (EVar 11) 24 24;
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000; KWord (SA (ELit 0) A_CANARY) (N.to_nat 8) (EVar 32)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ s (-1280) 1460); [evs; exact Hsp | lia | lia | lia | lia | exact HD].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal]. - krv Ha1.
      - apply kimg_ro. exact ROC. - apply kimg_relro. exact RRC. - unfold A_CANARY in *. (pose proof rr_canary_range; kwa FCAN). }
    xrun_at HR HK fx A_VSNPRINTF (seg_rom SEGS) 100%nat [A_MEMSET; A_VFPRINTF; VSN_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1. wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
    assert (ST1 : stores_in (zwin (s - 72) s) M M1) by (subst M1; stores_tower).
    assert (SV1 : slots SEGS M1 s [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]) by (subst M1; slots_tower).
    assert (Gcan1 : fld SEGS M1 (s - 48) 8 rr_canary) by (unfold fld; subst M1; peel).
    assert (Gcs1 : fld SEGS M1 (s - 72) 8 (s + 152)) by (unfold fld; subst M1; peel).
    assert (Gcn1 : fld SEGS M1 (s - 64) 8 23) by (unfold fld; subst M1; peel).
    regval HR1 (1%bv : reg) VSN_RET_MS X1. regval HR1 (2%bv : reg) (s - 304) X2.
    regval HR1 (10%bv : reg) (s - 304) X10. regval HR1 (11%bv : reg) 0 X11. regval HR1 (12%bv : reg) 232 X12.

    assert (HD1 : mdef M1 (s - 1280) 1460) by (eapply stores_in_mdef; [exact ST1 | exact HD]).
    destruct (u1_memset M1 (Z_to_bv 64 (s - 304)) (Z_to_bv 64 0) (Z_to_bv 64 VSN_RET_MS) 232 (seg_rom SEGS) R1
                ltac:(lia) ltac:(rewrite u64_of_Z by lia; lia)
                ltac:(replace (s - 304) with (s - 1280 + 976) by lia; eapply mdef_store_ok_off; [exact HD1 | lia | lia | lia | lia])
                ltac:(apply bv_eq; vm_compute; reflexivity) X10 X11 X12 X1)
      as (R2 & Hms2 & Y10 & AG2).
    replace u1_memset_entry with (Z_to_bv 64 A_MEMSET) in Hms2 by (apply bv_eq; vm_compute; reflexivity).
    set (M2 := wbytes M1 (Z_to_bv 64 (s - 304)) (repeat (cbyte (Z_to_bv 64 0)) (Z.to_nat 232))) in Hms2.
    assert (ZK2 : forall r, ~ In r ms_clob -> getr R2 r = getr R1 r) by (intros r Hr; exact (AG2 r Hr)).
    assert (ST2 : stores_in (zwin (s - 304) (s - 72)) M1 M2).
    { subst M2. apply stores_in_wbytes; [lia | rewrite repeat_length; lia | intros x Hx; rewrite repeat_length, Z2Nat.id in Hx by lia; unfold zwin; lia]. }
    assert (ST02 : stores_in (zwin (s - 304) s) M M2).
    { eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact ST2 | ..]; intros a Ha; unfold zwin in *; lia. }
    assert (T02 : forall a (n : nat) x, (a + Z.of_nat n <= s - 304 \/ s <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST02 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    assert (T12 : forall a (n : nat) x, (a + Z.of_nat n <= s - 304 \/ s - 72 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M1 a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST2 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    assert (Zf : forall d (n : nat), 0 <= d -> d + Z.of_nat n <= 232 -> (n = 8 \/ n = 4 \/ n = 1)%nat -> fld SEGS M2 (s - 304 + d) n 0).
    { intros d n Hd Hdn Hn. subst M2. change (Z.to_nat 232) with 232%nat. apply fld_zero_of_repeat; [lia | cbn; lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hn]. }

    assert (Z2 : getr R2 2%bv = Z_to_bv 64 (s - 304)) by (rewrite ZK2 by ninl; exact X2).
    assert (Z8 : getr R2 8%bv = Z_to_bv 64 (s + 48)) by (rewrite ZK2 by ninl; regval HR1 (8%bv : reg) (s + 48) X; exact X).
    assert (Z9 : getr R2 9%bv = Z_to_bv 64 (s + 176)) by (rewrite ZK2 by ninl; regval HR1 (9%bv : reg) (s + 176) X; exact X).
    assert (Z19 : getr R2 19%bv = Z_to_bv 64 (s + 152)) by (rewrite ZK2 by ninl; regval HR1 (19%bv : reg) (s + 152) X; exact X).
    assert (Z18 : getr R2 18%bv = Z_to_bv 64 A_CANARY) by (rewrite ZK2 by ninl; regval HR1 (18%bv : reg) A_CANARY X; exact X).
    set (E2 := Eseed R2 []).
    assert (HR2 : regs_ok E2 (srs sr_id [(8%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 352)); (9%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 480)); (19%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 456))]) R2) by srs_ok.
    assert (HK2 : know_ok SEGS E2 M2
      [KWr (SA (EVar 2) (-976)) (ELit 1460); KRange (EVar 2) (2 ^ 32 + 976) (2 ^ 47 - 484); KAlign (EVar 2) 16;
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (s - 304) (-976) 1460); [evs; exact Z2 | lia | lia | lia | lia | replace (s - 304 + -976) with (s - 1280) by lia; eapply stores_in_mdef; [exact ST02 | exact HD]].
      - krv Z2. - eapply kalign_var; [evs; exact Z2 | lia | lia | mlia].
      - apply kimg_ro. eapply ro_clear_hi; [exact ROC | exact ST02 | intros a Ha; unfold zwin in Ha; lia].
      - apply kimg_relro. eapply relro_clear_hi; [exact RRC | exact ST02 | intros a Ha; unfold zwin in Ha; lia]. }
    xrun_at HR2 HK2 fx VSN_RET_MS (seg_rom SEGS) 100%nat [A_MEMSET; A_VFPRINTF; VSN_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK2. rename R' into R3. rename HR' into HR3. rename Hms into Hms3. wnorm_in Hms3.
    lazymatch type of Hms3 with msteps _ _ (mkst _ _ ?mm _) => set (M3 := mm) in Hms3 end.
    assert (ST3 : stores_in (fun a => zwin (s - 232) (s - 144) a \/ zwin (s + 152) (s + 153) a) M2 M3) by (subst M3; stores_tower).
    assert (ST03 : stores_in (fun a => zwin (s - 304) s a \/ zwin (s + 152) (s + 153) a) M M3).
    { eapply (stores_in_join _ _ _ M M2 M3); [exact ST02 | exact ST3 | ..]; intros a Ha; cbv beta in *; unfold zwin in *; lia. }
    assert (T23 : forall a (n : nat) x, (a + Z.of_nat n <= s - 232 \/ s - 144 <= a) -> a + Z.of_nat n <= s + 152 -> 0 <= a -> fld SEGS M2 a n x -> fld SEGS M3 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST3 | intros y Hy; cbv beta; unfold zwin; lia | lia | lia | exact HF]. }
    assert (T03 : forall a (n : nat) x, (a + Z.of_nat n <= s - 304 \/ s <= a) -> (a + Z.of_nat n <= s + 152 \/ s + 153 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M3 a n x).
    { intros a n x G1 G2 G3 G4 HF. eapply (fld_via_stores SEGS); [exact ST03 | intros y Hy; cbv beta; unfold zwin; lia | lia | lia | exact HF]. }
    pose proof (T23 (s - 304 + 0) 4%nat 0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) (Zf 0 4%nat ltac:(lia) ltac:(cbn; lia) ltac:(lia))) as Gflags3. replace (s - 304 + 0) with (s - 304) in Gflags3 by lia.
    pose proof (Zf 96 8%nat ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Gbsz2. assert (Gbsz3 : fld SEGS M3 (s - 304 + 96) 8 0) by (unfold fld in Gbsz2 |- *; subst M3; peel; exact Gbsz2).
    pose proof (Zf 136 4%nat ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Gmode2. assert (Gmode3 : fld SEGS M3 (s - 304 + 136) 4 0) by (unfold fld in Gmode2 |- *; subst M3; peel; exact Gmode2).
    assert (Gwrite3 : fld SEGS M3 (s - 304 + 72) 8 A_SN_WRITE) by (unfold fld; subst M3; peel).
    assert (Gbuf3 : fld SEGS M3 (s - 304 + 88) 8 (s - 304 + 255)) by (unfold fld; subst M3; peel).
    assert (EW4 : word_to_le_bytes 4 (Z_to_bv 64 (2 ^ 32 - 1)) = word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)).
    { rewrite (w2lb_mod 4 18446744073709551615) by lia. reflexivity. }
    assert (Glock3 : fld SEGS M3 (s - 304 + 140) 4 (2 ^ 32 - 1)) by (unfold fld; rewrite EW4; subst M3; peel).
    assert (Glbf3 : fld SEGS M3 (s - 304 + 144) 4 (2 ^ 32 - 1)) by (unfold fld; rewrite EW4; subst M3; peel).
    assert (Gcookie3 : fld SEGS M3 (s - 304 + 152) 8 (s - 304 + 232)) by (unfold fld; subst M3; peel).
    pose proof (T23 (s - 72) 8%nat (s + 152) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) (T12 (s - 72) 8%nat (s + 152) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Gcs1)) as Gcs3.
    replace (s - 72) with (s - 304 + 232) in Gcs3 by lia. replace (s + 152) with (s - 304 + 456) in Gcs3 by lia.
    pose proof (T23 (s - 64) 8%nat 23 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) (T12 (s - 64) 8%nat 23 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Gcn1)) as Gcn3.
    replace (s - 64) with (s - 304 + 240) in Gcn3 by lia.
    pose proof (T03 (s + 48) 8%nat v ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Fv) as Fv3. replace (s + 48) with (s - 304 + 352) in Fv3 by lia.
    pose proof (T03 (s + 176) 1%nat 37 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F0) as F03. replace (s + 176) with (s - 304 + 480) in F03 by lia.
    pose proof (T03 (s + 177) 1%nat 108 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F1) as F13. replace (s + 177) with (s - 304 + 481) in F13 by lia.
    pose proof (T03 (s + 178) 1%nat conv ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F2) as F23. replace (s + 178) with (s - 304 + 482) in F23 by lia.
    pose proof (T03 (s + 179) 1%nat 0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F3) as F33. replace (s + 179) with (s - 304 + 483) in F33 by lia.
    assert (ROC3 : ro_clear Ly.L M3) by (eapply ro_clear_hi; [exact ROC | exact ST03 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia]).
    assert (RRC3 : relro_clear M3) by (eapply relro_clear_hi; [exact RRC | exact ST03 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia]).
    assert (FCAN3 : fld SEGS M3 A_CANARY 8 rr_canary) by (eapply (fld_via_stores SEGS); [exact ST03 | intros y Hy; cbv beta; unfold zwin, A_CANARY in *; lia | unfold A_CANARY; lia | unfold A_CANARY; cbn; lia | exact FCAN]).
    assert (HD3 : mdef M3 (s - 304 - 976) 1460) by (replace (s - 304 - 976) with (s - 1280) by lia; eapply stores_in_mdef; [exact ST03 | exact HD]).
    regval HR3 (1%bv : reg) VSN_RET_VF Y1. regval HR3 (2%bv : reg) (s - 304) Y2. regval HR3 (10%bv : reg) (s - 304) Y10'.
    regval HR3 (11%bv : reg) (s - 304 + 480) Y11. regval HR3 (12%bv : reg) (s - 304 + 352) Y12.
    pose proof (@vfprintf_sn fx RRND R3 M3 (s - 304) VSN_RET_VF v conv Y1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold VSN_RET_VF; lia) Y2 Y10' Y11 Y12
                  ltac:(lia) ltac:(lia) ltac:(mlia) HD3 Fv3 Hv F03 F13 F23 F33 Hconv
                  Gflags3 Gwrite3 Gbuf3 Gbsz3 Gmode3 Glock3 Glbf3 Gcookie3 Gcs3 Gcn3 ROC3 RRC3 FCAN3) as LV.
    destruct LV as (nc & R4 & M4 & Hms4 & P10 & Pnc & PK & PST).

    assert (ST04 : stores_in (fun a => zwin (s - 1280) s a \/ zwin (s + 152) (s + 152 + nc + 1) a) M M4).
    { eapply (stores_in_join _ _ _ M M3 M4); [exact ST03 | exact PST | ..]; intros a Ha; cbv beta in *; unfold zwin in *; lia. }
    assert (SV4 : slots SEGS M4 s [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
    { eapply slots_agree; [exact SV1 | cbn; lia | lia |]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul].
      assert (A12 : agree_on (zwin (s - 40) s) M1 M2) by (eapply stores_in_agree; [exact ST2 | intros b Hb; unfold zwin in *; lia]).
      assert (A23 : agree_on (zwin (s - 40) s) M2 M3) by (eapply stores_in_agree; [exact ST3 | intros b Hb; cbv beta; unfold zwin in *; lia]).
      assert (A34 : agree_on (zwin (s - 40) s) M3 M4) by (eapply stores_in_agree; [exact PST | intros b Hb; cbv beta; unfold zwin in *; lia]).
      intros b Hb. rewrite (A34 b Hb), (A23 b Hb). exact (A12 b Hb). }
    assert (Gcan4 : fld SEGS M4 (s - 48) 8 rr_canary).
    { eapply (fld_via_stores SEGS); [exact PST | intros y Hy; cbv beta; unfold zwin; lia | lia | cbn; lia |].
      apply T23; [cbn; lia | cbn; lia | lia |]. apply T12; [cbn; lia | lia | cbn; lia | exact Gcan1]. }
    assert (FCAN4 : fld SEGS M4 A_CANARY 8 rr_canary) by (eapply (fld_via_stores SEGS); [exact ST04 | intros y Hy; cbv beta; unfold zwin, A_CANARY in *; lia | unfold A_CANARY; lia | unfold A_CANARY; cbn; lia | exact FCAN]).
    assert (V2' : getr R4 2%bv = Z_to_bv 64 (s - 304)) by (rewrite (PK 2%bv) by inl; exact Y2).
    assert (V18 : getr R4 18%bv = Z_to_bv 64 A_CANARY) by (rewrite (PK 18%bv) by inl; rewrite (syms_id_sound R2 _ _ R3 [18%bv] HR3 eq_refl 18%bv ltac:(inl)); exact Z18).
    set (E4 := Eseed R4 [Z_to_bv 64 nc; Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; Z_to_bv 64 rr_canary]).
    assert (HR4 : regs_ok E4 sr_id R4) by (apply regs_ok_seed).
    assert (HK4 : know_ok SEGS E4 M4
      [KWr (SA (EVar 2) (-976)) (ELit 1460); KRange (EVar 2) (2 ^ 32 + 976) (2 ^ 47 - 484); KAlign (EVar 2) 16;
       KRange (EVar 18) A_CANARY A_CANARY;
       KWord (SA (EVar 2) 256) (N.to_nat 8) (EVar 38); KWord (SA (ELit 0) A_CANARY) (N.to_nat 8) (EVar 38);
       KWord (SA (EVar 2) 296) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 288) (N.to_nat 8) (EVar 34); KWord (SA (EVar 2) 280) (N.to_nat 8) (EVar 35);
       KWord (SA (EVar 2) 272) (N.to_nat 8) (EVar 36); KWord (SA (EVar 2) 264) (N.to_nat 8) (EVar 37);
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (s - 304) (-976) 1460); [evs; exact V2' | lia | lia | lia | lia | replace (s - 304 + -976) with (s - 1280) by lia; eapply stores_in_mdef; [exact ST04 | exact HD]].
      - krv V2'. - eapply kalign_var; [evs; exact V2' | lia | lia | mlia].
      - unfold A_CANARY in *; krv V18.
      - (pose proof rr_canary_range; kwv Gcan4 V2'). - unfold A_CANARY in *; (pose proof rr_canary_range; kwa FCAN4).
      - kwe (SV4 0%nat ltac:(cbn [length]; lia)) V2'. - kwe (SV4 1%nat ltac:(cbn [length]; lia)) V2'. - kwe (SV4 2%nat ltac:(cbn [length]; lia)) V2'.
      - kwe (SV4 3%nat ltac:(cbn [length]; lia)) V2'. - kwe (SV4 4%nat ltac:(cbn [length]; lia)) V2'.
      - apply kimg_ro. eapply ro_clear_hi; [exact ROC | exact ST04 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia].
      - apply kimg_relro. eapply relro_clear_hi; [exact RRC | exact ST04 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; lia]. }
    xrun_at HR4 HK4 fx VSN_RET_VF (seg_rom SEGS) 100%nat [A_MEMSET; A_VFPRINTF; VSN_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK4. rename Hms into Hms5.
    regval HR' (1%bv : reg) ret T1. regval HR' (10%bv : reg) nc T10.
    pose proof (ret_at SEGS VSN_RETPC R' M4 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) T1 Hret) as Hms6.
    exists nc, R', M4. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
      eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5 | exact Hms6]. }
    split; [exact T10|]. split; [exact Pnc|]. split; [|exact ST04].
    intros r Hr. unfold leaf_kept in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR' PK HR3 ZK2 HR1|]). destruct Hr.
  Qed.
End Vsn.
End VsnPrintfU1.

Module SnPrintfLU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTail OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DFactsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLoopsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.NumLeafU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.SnWriteU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1.PcPass1U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2BU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2CU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DoPutDefsU1.VfPrintfU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DoPutDefsU1.VsnPrintfU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S. Import NumLoopsU1.NDig.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition SNP_RET_VSN : Z := 0xc9ba0.
Definition SNP_RETPC : Z := 0xc9bcc.

Definition TD_BYTES : list Z := [0xe0; 0x26; 0x12; 0; 0; 0; 0; 0].
Definition td_pinned (M : mem) : Prop :=
  forall i, 0 <= i < 8 -> M (Z_to_bv 64 (TD_LOCALE + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) TD_BYTES 0)).

Lemma td_pinned_fld : forall M, td_pinned M -> fld SEGS M TD_LOCALE 8 GLOBAL_LOCALE.
Proof.
  intros M H. unfold fld.
  transitivity (Some (map (Z_to_bv 8) TD_BYTES)); [| f_equal; apply DiagPins.byte_list_eq; vm_compute; reflexivity].
  change 8%nat with (length (map (Z_to_bv 8) TD_BYTES)). apply rdn_of_pointwise; [unfold TD_LOCALE; lia | unfold TD_LOCALE; cbn; lia |].
  intros k Hk. rewrite (H (Z.of_nat k)) by (cbn in Hk; lia). rewrite Nat2Z.id.
  do 8 (destruct k as [|k]; [reflexivity|]). cbn in Hk. lia.
Qed.

Lemma td_pinned_mdef : forall M, td_pinned M -> mdef M TD_LOCALE 8.
Proof. intros M H i Hi. rewrite (H i Hi). discriminate. Qed.

Section Snp.
  Context {fx : FPState}.
Context {RRND : RunRandom}.
  Variables (R : bvmap 5 word) (M : mem) (ssp ret v conv : Z).

  Hypothesis Hra : getr R 1%bv = Z_to_bv 64 ret.
  Hypothesis Hret : ret_ok (Z_to_bv 64 ret).
  Hypothesis Hretr : 0 <= ret < 2 ^ 64.
  Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 ssp.
  Hypothesis Htp : getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L).
  Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 (ssp + 72).
  Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 24.
  Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 C_LOCALE_OBJ.
  Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 (ssp + 96).
  Hypothesis Ha4 : getr R 14%bv = Z_to_bv 64 v.
  Hypothesis Hslo : 2 ^ 32 <= ssp - 1360.
  Hypothesis Hshi : ssp + 100 < 2 ^ 47.
  Hypothesis Hal : ssp mod 16 = 0.
  Hypothesis HD : mdef M (ssp - 1360) 1460.
  Hypothesis Hv : 0 <= v < 2 ^ 64.
  Hypothesis F0 : fld SEGS M (ssp + 96) 1 37.
  Hypothesis F1 : fld SEGS M (ssp + 97) 1 108.
  Hypothesis F2 : fld SEGS M (ssp + 98) 1 conv.
  Hypothesis F3 : fld SEGS M (ssp + 99) 1 0.
  Hypothesis Hconv : conv = 117 \/ conv = 100 \/ conv = 120.
  Hypothesis ROC : ro_clear Ly.L M.
  Hypothesis RRC : relro_clear M.
  Hypothesis FCAN : fld SEGS M A_CANARY 8 rr_canary.
  Hypothesis HTD : td_pinned M.

  Definition snp_post (nc : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
    getr R' 10%bv = Z_to_bv 64 nc /\ 1 <= nc <= 21
    /\ (forall r, In r leaf_kept -> getr R' r = getr R r)
    /\ stores_in (fun a => zwin (ssp - 1360) ssp a \/ zwin (ssp + 72) (ssp + 72 + nc + 1) a) M M'
    /\ td_pinned M'.

  Lemma snprintf_l : exists nc R' M',
    msteps SEGS (@mkst fx R (Z_to_bv 64 A_SNPRINTF_L) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) /\ snp_post nc R' M'.
  Proof using fx RRND R M ssp ret v conv Hra Hret Hretr Hsp Htp Ha0 Ha1 Ha2 Ha3 Ha4 Hslo Hshi Hal HD Hv F0 F1 F2 F3 Hconv ROC RRC FCAN HTD.
    cbn [ly_tp Ly.L] in Htp.
    pose proof (td_pinned_fld M HTD) as FTD. pose proof (td_pinned_mdef M HTD) as DTD.
    set (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id [(10%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 72)); (13%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 96))]) R) by srs_ok.
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-1360)) (ELit 1460); KRange (EVar 2) (2 ^ 32 + 1360) (2 ^ 47 - 100); KAlign (EVar 2) 16;
       KRange (EVar 4) 0x102418 0x102418; KRange (EVar 11) 24 24; KRange (EVar 12) C_LOCALE_OBJ C_LOCALE_OBJ;
       KWord (SA (ELit 0) TD_LOCALE) (N.to_nat 8) (ELit GLOBAL_LOCALE); KWr (SA (ELit 0) TD_LOCALE) (ELit 8);
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ ssp (-1360) 1460); [evs; exact Hsp | lia | lia | lia | lia | exact HD].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal].
      - krv Htp. - krv Ha1. - unfold C_LOCALE_OBJ in *; krv Ha2.
      - unfold TD_LOCALE, GLOBAL_LOCALE in *. kwa FTD.
      - unfold TD_LOCALE in *. apply kwr_abs_of_mdef; [lia | lia | lia | exact DTD].
      - apply kimg_ro. exact ROC. - apply kimg_relro. exact RRC. }
    xrun_at HR HK fx A_SNPRINTF_L (seg_rom SEGS) 100%nat [A_VSNPRINTF; SNP_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1. wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
    assert (ST1 : stores_in (fun a => zwin (ssp - 80) ssp a \/ zwin TD_LOCALE (TD_LOCALE + 8) a) M M1) by (subst M1; unfold TD_LOCALE; stores_tower).
    assert (SV1 : slots SEGS M1 (ssp - 32) [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]) by (subst M1; slots_tower).
    assert (Gv1 : fld SEGS M1 (ssp - 32) 8 v) by (unfold fld; subst M1; gnorm (14%bv : reg); rewrite Ha4; peel).
    assert (Gtd1 : fld SEGS M1 TD_LOCALE 8 C_LOCALE_OBJ) by (unfold fld, TD_LOCALE; subst M1; peel).
    assert (HD1 : mdef M1 (ssp - 1360) 1460) by (eapply stores_in_mdef; [exact ST1 | exact HD]).
    assert (WOK : forall a, (zwin (ssp - 80) ssp a \/ zwin TD_LOCALE (TD_LOCALE + 8) a) -> 2 ^ 32 <= a \/ 0xef000 <= a < 0x124000) by (intros a Ha; unfold zwin, TD_LOCALE in Ha; lia).
    assert (T01 : forall a (n : nat) x, (a + Z.of_nat n <= ssp - 80 \/ ssp <= a) -> 2 ^ 32 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M1 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; cbv beta; unfold zwin, TD_LOCALE; lia | lia | lia | exact HF]. }
    regval HR1 (1%bv : reg) SNP_RET_VSN X1. regval HR1 (2%bv : reg) (ssp - 80) X2.
    regval HR1 (10%bv : reg) (ssp - 80 + 152) X10. regval HR1 (11%bv : reg) 24 X11. regval HR1 (12%bv : reg) (ssp - 80 + 176) X12. regval HR1 (13%bv : reg) (ssp - 80 + 48) X13.
    pose proof (T01 (ssp + 96) 1%nat 37 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F0) as F0'. replace (ssp + 96) with (ssp - 80 + 176) in F0' by lia.
    pose proof (T01 (ssp + 97) 1%nat 108 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F1) as F1'. replace (ssp + 97) with (ssp - 80 + 177) in F1' by lia.
    pose proof (T01 (ssp + 98) 1%nat conv ltac:(lia) ltac:(lia) ltac:(cbn; lia) F2) as F2'. replace (ssp + 98) with (ssp - 80 + 178) in F2' by lia.
    pose proof (T01 (ssp + 99) 1%nat 0 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F3) as F3'. replace (ssp + 99) with (ssp - 80 + 179) in F3' by lia.
    replace (ssp - 32) with (ssp - 80 + 48) in Gv1 by lia.
    assert (ROC1 : ro_clear Ly.L M1) by (eapply ro_clear_stores'; [exact ROC | exact ST1 | exact WOK]).
    assert (RRC1 : relro_clear M1) by (eapply relro_clear_stores'; [exact RRC | exact ST1 | exact WOK]).
    assert (FCAN1 : fld SEGS M1 A_CANARY 8 rr_canary) by (eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; cbv beta; unfold zwin, A_CANARY, TD_LOCALE in *; lia | unfold A_CANARY; lia | unfold A_CANARY; cbn; lia | exact FCAN]).
    assert (HD1' : mdef M1 (ssp - 80 - 1280) 1460) by (replace (ssp - 80 - 1280) with (ssp - 1360) by lia; exact HD1).
    pose proof (@vsnprintf24 fx RRND R1 M1 (ssp - 80) SNP_RET_VSN v conv X1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold SNP_RET_VSN; lia) X2 X10 X11 X12 X13
                  ltac:(lia) ltac:(lia) ltac:(mlia) HD1' Gv1 Hv F0' F1' F2' F3' Hconv ROC1 RRC1 FCAN1) as LV.
    destruct LV as (nc & R2 & M2 & Hms2 & P10 & Pnc & PK & PST).

    assert (ST02 : stores_in (fun a => zwin (ssp - 1360) ssp a \/ zwin TD_LOCALE (TD_LOCALE + 8) a \/ zwin (ssp + 72) (ssp + 72 + nc + 1) a) M M2).
    { eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact PST | ..]; intros a Ha; cbv beta in *; unfold zwin in *; lia. }
    assert (T12 : forall a (n : nat) x, (a + Z.of_nat n <= ssp - 1360 \/ ssp - 80 <= a) -> a + Z.of_nat n <= ssp + 72 -> 0 <= a -> fld SEGS M1 a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact PST | intros y Hy; cbv beta; unfold zwin; lia | lia | lia | exact HF]. }
    assert (Gtd2 : fld SEGS M2 TD_LOCALE 8 C_LOCALE_OBJ) by (eapply (fld_via_stores SEGS); [exact PST | intros y Hy; cbv beta; unfold zwin, TD_LOCALE in *; lia | unfold TD_LOCALE; lia | unfold TD_LOCALE; cbn; lia | exact Gtd1]).
    assert (DTD2 : mdef M2 TD_LOCALE 8) by (eapply stores_in_mdef; [exact PST | eapply stores_in_mdef; [exact ST1 | exact DTD]]).
    assert (SV2 : slots SEGS M2 (ssp - 32) [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
    { eapply slots_agree; [exact SV1 | cbn; lia | lia |]. eapply stores_in_agree; [exact PST|]. intros b Hb. unfold zwin in Hb. cbn in Hb. cbv beta. unfold zwin. lia. }
    assert (Y2' : getr R2 2%bv = Z_to_bv 64 (ssp - 80)) by (rewrite (PK 2%bv) by inl; exact X2).
    assert (Y4 : getr R2 4%bv = Z_to_bv 64 0x102418) by (rewrite (PK 4%bv) by inl; regval HR1 (4%bv : reg) 0x102418 X; exact X).
    assert (Y19 : getr R2 19%bv = Z_to_bv 64 (2 ^ 64 - 1)) by (rewrite (PK 19%bv) by inl; regval HR1 (19%bv : reg) (2 ^ 64 - 1) X; exact X).
    set (E2 := Eseed R2 [Z_to_bv 64 nc; Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
    assert (HR2 : regs_ok E2 sr_id R2) by (apply regs_ok_seed).
    assert (HK2 : know_ok SEGS E2 M2
      [KWr (SA (EVar 2) (-1280)) (ELit 1460); KRange (EVar 2) (2 ^ 32 + 1280) (2 ^ 47 - 180); KAlign (EVar 2) 16;
       KRange (EVar 4) 0x102418 0x102418; KRange (EVar 19) (2 ^ 64 - 1) (2 ^ 64 - 1); KRange (EVar 10) 1 21;
       KWord (SA (ELit 0) TD_LOCALE) (N.to_nat 8) (ELit C_LOCALE_OBJ); KWr (SA (ELit 0) TD_LOCALE) (ELit 8);
       KWord (SA (EVar 2) 40) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 32) (N.to_nat 8) (EVar 34); KWord (SA (EVar 2) 24) (N.to_nat 8) (EVar 35);
       KWord (SA (EVar 2) 16) (N.to_nat 8) (EVar 36); KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 37);
       KImg 0x10000 0xe8000; KImg 0xe8000 0xef000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (ssp - 80) (-1280) 1460); [evs; exact Y2' | lia | lia | lia | lia | replace (ssp - 80 + -1280) with (ssp - 1360) by lia; eapply stores_in_mdef; [exact ST02 | exact HD]].
      - krv Y2'. - eapply kalign_var; [evs; exact Y2' | lia | lia | mlia].
      - krv Y4. - krv Y19. - krv P10.
      - unfold TD_LOCALE, C_LOCALE_OBJ in *. kwa Gtd2.
      - unfold TD_LOCALE in *. apply kwr_abs_of_mdef; [lia | lia | lia | exact DTD2].
      - kwe (SV2 0%nat ltac:(cbn [length]; lia)) Y2'. - kwe (SV2 1%nat ltac:(cbn [length]; lia)) Y2'. - kwe (SV2 2%nat ltac:(cbn [length]; lia)) Y2'.
      - kwe (SV2 3%nat ltac:(cbn [length]; lia)) Y2'. - kwe (SV2 4%nat ltac:(cbn [length]; lia)) Y2'.
      - apply kimg_ro. eapply ro_clear_stores'; [exact ROC | exact ST02 | intros a Ha; cbv beta in Ha; unfold zwin, TD_LOCALE in Ha; lia].
      - apply kimg_relro. eapply relro_clear_stores'; [exact RRC | exact ST02 | intros a Ha; cbv beta in Ha; unfold zwin, TD_LOCALE in Ha; lia]. }
    xrun_at HR2 HK2 fx SNP_RET_VSN (seg_rom SEGS) 100%nat [A_VSNPRINTF; SNP_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK2. rename Hms into Hms3. wnorm_in Hms3.
    lazymatch type of Hms3 with msteps _ _ (mkst _ _ ?mm _) => set (M3 := mm) in Hms3 end.
    regval HR' (1%bv : reg) ret T1. regval HR' (10%bv : reg) nc T10.
    pose proof (ret_at SEGS SNP_RETPC R' M3 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) T1 Hret) as Hms4.
    assert (PIN3 : td_pinned M3).
    { intros i Hi. subst M3. unfold TD_LOCALE. rewrite MemSplit.wbytes_inside; [| cbn; rewrite u64_of_Z by lia; lia | cbn; rewrite !u64_of_Z by lia; lia].
      rewrite !u64_of_Z by lia. replace (1057768 + i - 1057768) with i by lia.
      assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
      destruct Hi8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; (f_equal; apply bv_eq; vm_compute; reflexivity). }
    exists nc, R', M3. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3 | exact Hms4]. }
    split; [exact T10|]. split; [exact Pnc|]. split.
    { intros r Hr. unfold leaf_kept in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR' PK HR1|]). destruct Hr. }
    split; [|exact PIN3].
    assert (ST03 : stores_in (fun a => zwin (ssp - 1360) ssp a \/ zwin TD_LOCALE (TD_LOCALE + 8) a \/ zwin (ssp + 72) (ssp + 72 + nc + 1) a) M M3).
    { eapply (stores_in_join _ _ _ M M2 M3); [exact ST02 | subst M3; unfold TD_LOCALE; apply stores_in_wbytes; [lia | cbn; lia | intros x Hx; exact Hx] | ..];
        intros a Ha; cbv beta in *; cbn in Ha; unfold zwin, TD_LOCALE in *; lia. }
    eapply stores_in_shrink; [exact ST03|]. intros a Ha Hw Hnw. cbv beta in Hw, Hnw.
    assert (Htd : zwin TD_LOCALE (TD_LOCALE + 8) a) by tauto. unfold zwin in Htd.
    replace a with (TD_LOCALE + (a - TD_LOCALE)) by lia. rewrite (PIN3 (a - TD_LOCALE)) by lia. rewrite (HTD (a - TD_LOCALE)) by lia. reflexivity.
  Qed.
End Snp.
End SnPrintfLU1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import RunsLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac DiagU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DFactsU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DFactsU1.DiagPinsU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DFactsU1 NumLoopsU1 NumLeafU1 SnWriteU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.PcPass2AU1.PcPass1U1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import PcPass2AU1 PcPass2BU1 PcPass2CU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DoPutDefsU1.VfPrintfU1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DoPutDefsU1.VsnPrintfU1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DoPutDefsU1.SnPrintfLU1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S. Import NumLoopsU1.NDig.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition A_PAD_XS_RET : Z := 0xa0fb8.
Definition WG_RET_WIDEN : Z := 0xa305c.

Lemma td_pinned_of_pins : forall M, pins D_DIAG M -> td_pinned M.
Proof.
  intros M HP i Hi. unfold TD_LOCALE.
  assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; (apply HP; [lia | vm_compute; reflexivity]).
Qed.

Section Defs.
  Variables (R : bvmap 5 word) (M : mem) (ssp ds ret : Z) (fillw : word) (padra : Z).

  Record dpm (nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop := DPM {
    dp_st : stores_in (zwin (ssp - 1520) ssp) M M1;
    dp_td : td_pinned M1;
    dp_sv : slots SEGS M1 ssp [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv];
    dp_padsv : slots SEGS M1 (ssp - 160) [Z_to_bv 64 padra; fillw; Z_to_bv 64 (ds + 112); Z_to_bv 64 (ds + 8); Z_to_bv 64 (ssp - 88 + nc); Z_to_bv 64 (ssp - 88); Z_to_bv 64 0x100e20; getr R 22%bv; getr R 23%bv];
    dp_r1 : getr R1 1%bv = Z_to_bv 64 A_PAD_XS_RET; dp_r2 : getr R1 2%bv = Z_to_bv 64 (ssp - 256);
    dp_r3 : getr R1 3%bv = getr R 3%bv; dp_r4 : getr R1 4%bv = getr R 4%bv;
    dp_r8 : getr R1 8%bv = Z_to_bv 64 (ds + 8); dp_r9 : getr R1 9%bv = Z_to_bv 64 (ds + 112);
    dp_r10 : getr R1 10%bv = Z_to_bv 64 (ds + 8); dp_r11 : getr R1 11%bv = Z_to_bv 64 (ssp - 133); dp_r12 : getr R1 12%bv = Z_to_bv 64 nc;
    dp_r19 : getr R1 19%bv = Z_to_bv 64 nc;
    dp_cs : forall r, In r [24; 25; 26; 27]%bv -> getr R1 r = getr R r;
    dp_nc : 1 <= nc <= 21 }.

  Record dps (nc : Z) (R2 : bvmap 5 word) (M2 : mem) : Prop := DPS {
    ds_st : stores_in (zwin (ssp - 1520) ssp) M M2;
    ds_td : td_pinned M2;
    ds_sv : slots SEGS M2 ssp [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv];
    ds_r2 : getr R2 2%bv = Z_to_bv 64 (ssp - 160); ds_r3 : getr R2 3%bv = getr R 3%bv; ds_r4 : getr R2 4%bv = getr R 4%bv;
    ds_r8 : getr R2 8%bv = fillw; ds_r9 : getr R2 9%bv = Z_to_bv 64 (ds + 112); ds_r10 : getr R2 10%bv = Z_to_bv 64 nc;
    ds_r18 : getr R2 18%bv = Z_to_bv 64 (ds + 8); ds_r20 : getr R2 20%bv = Z_to_bv 64 (ssp - 88); ds_r21 : getr R2 21%bv = Z_to_bv 64 0x100e20;
    ds_cs : forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R2 r = getr R r;
    ds_nc : 1 <= nc <= 21 }.
End Defs.
