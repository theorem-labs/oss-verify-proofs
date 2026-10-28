(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128P5_b PnARel3_b Ba0_code_b30ac_b30b0_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADF.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem epilogue (E : dve) (X : dkc L ar HI E) (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) (ptr ec : Z) :
  dst L ar HI E Mc modelc LKc Ac -> PNADD.stE (vR E) (vsp E) (vF E) ptr ec Rc -> vfirst E <= ptr <= vfirst E + 42 -> 0 <= ec < 2 ^ 64 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb46b0 Mc modelc) (vK E).
Proof.
  intros ST RG Hptr Hec.
  dgeom L ar HI E X. dfacts L ar C HI LY HIok E X ST.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct RG as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q24 & Q25). unfold PNADD.SH, PNADD.SBv in Q23.
  pose proof ST as (BI & DF & AF & DV & AV & BASE & ERR & C128 & ZSIG).
  pose proof (c_G L ar HI E X) as XG. pose proof XG as G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8' GFBIG GF32' GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  set (sh := vF E / 8 + 2147450880) in *.
  assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296) by (subst sh; clear - E0; lia).
  assert (Y1 : 4096 <= vF E <= 140737488354816) by (clear - GFF1; lia).
  assert (Y2 : (65536 + 6840320 <= sh \/ sh + 64 <= 65536)) by (left; clear - SHR; lia).
  assert (Yp : 0 <= ptr < 2 ^ 64) by (clear - Hptr GF1; lia).
  LeanFeed.pfeed P (PNADP5.adkE1_conc fx Rc MV (fun j => match j with 2%nat => vsp E | 50%nat => vF E | 52%nat => ptr | 53%nat => ec | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11 & HMAG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (vF E <= a < vF E + 8) -> ~ (sh <= a < sh + 64) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha N1 N2. apply FRZ1; [exact Ha| intros Y; apply N2; clear - Y; lia| intros Y; apply N1; clear - Y; lia]. }
  assert (AGI1 : forall i, 65536 <= i < 6905856 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi. apply AG1; [clear - Hi; lia| clear - Hi GFFI; lia| clear - Hi SHR; lia]. }
  assert (IMGC1 : L5.img_clear M1v 1249280 1282048) by (intros i Hi; rewrite AGI1 by (clear - Hi; lia); apply MIMGC; exact Hi).
  assert (CSB1 : L5.u64_at RSEGS M1v 1309752 2147450880) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact MCSB]).
  assert (CUAR1 : L5.u32_at RSEGS M1v 1309760 1) by (apply (PMF.u32_at_agree RSEGS MV M1v); [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact MCUAR]).
  assert (RMS1 : L5.u64_at RSEGS M1v 1283280 1219844) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact MRMS]).
  assert (FSHW1 : L5.writable RSEGS M1v sh 64) by (eapply L5.writable_grows; [exact MG1| exact MFSW]).
  (* [comment removed for export] *)
  destruct (PNAREL.setshadow_f5_run fx1 R1 M1v sh 64 739096 IMGC1 CSB1 CUAR1 RMS1 T10 T11 T1 ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - SHR; lia) ltac:(clear - SHR; lia) FSHW1)
    as (fx2 & R2 & MS2 & KP2).
  set (M2v := wbytes M1v (Z_to_bv 64 sh) (repeat (Z_to_bv 8 245) (Z.to_nat 64))) in *.
  assert (MG2 : mem_grows M1v M2v) by (apply wbytes_grows).
  assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + 64) -> M2v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
  { intros a Ha Hn. subst M2v. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia.
    rewrite repeat_length, !L5.unsigned_lit by (clear - SHR Ha; lia). clear - Hn. lia. }
  assert (AGM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (vF E <= a < vF E + 8) -> ~ (sh <= a < sh + 64) -> M2v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha N1 N2. rewrite AG2; [apply AG1; assumption| exact Ha| exact N2]. }
  assert (MG12 : mem_grows MV M2v) by (intros x Hx; apply MG2; apply MG1; exact Hx).
  (* [comment removed for export] *)
  assert (K12 : forall j, In j PNAREL.KEPT -> getr R2 (reg j) = getr Rc (reg j)).
  { intros j Hj. rewrite (KP2 j Hj). apply KS1. revert j Hj. apply (L5K.incl_b PNAREL.KEPT). vm_compute. reflexivity. }
  assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (vsp E - 256)) by (rewrite K12 by inl; exact Q2).
  assert (B8 : getr R2 (reg 8) = Z_to_bv 64 (vsp E)) by (rewrite K12 by inl; exact Q8).
  assert (B26 : getr R2 (reg 26) = Z_to_bv 64 (vF E)) by (rewrite K12 by inl; exact Q26). assert (B27 : getr R2 (reg 27) = Z_to_bv 64 (vF E)) by (rewrite K12 by inl; exact Q27).
  assert (B24 : getr R2 (reg 24) = Z_to_bv 64 ptr) by (rewrite K12 by inl; exact Q24).
  assert (B25 : getr R2 (reg 25) = Z_to_bv 64 ec) by (rewrite K12 by inl; exact Q25).
  assert (WS2 : L5.writable RSEGS M2v (vsp E - 256) 256) by (eapply L5.writable_grows; [exact MG12| exact MWS]).
  assert (FLW2 : L5.writable RSEGS M2v (vfl E) 1) by (eapply L5.writable_grows; [exact MG12| exact MFLW]).
  assert (FLC2 : L5.u64_at RSEGS M2v (vF E + 504) (vfl E)).
  { eapply L5C.u64_at_agree; [intros i Hi; apply AGM2; [clear - Hi GFF1; lia| clear - Hi; lia| clear - Hi GFFSH SHR; lia]| clear - GFF1; lia| clear - GFF1; lia| exact MFLC]. }
  assert (SVX : forall a v, vsp E - 104 <= a -> a + 8 <= vsp E -> L5.u64_at RSEGS MV a v -> L5.u64_at RSEGS M2v a v).
  { intros a v H1 H2 U. eapply L5C.u64_at_agree; [intros i Hi; apply AGM2; [clear - Hi H1 H2 SR; lia| clear - Hi H1 H2 GFFS; lia| clear - Hi H1 H2 SR SHR; lia]| clear - H1 SR; lia| clear - H2 SR; lia| exact U]. }
  apply SVX in MS8; [| clear; lia| clear; lia]. apply SVX in MS16; [| clear; lia| clear; lia]. apply SVX in MS24; [| clear; lia| clear; lia]. apply SVX in MS32; [| clear; lia| clear; lia].
  apply SVX in MS40; [| clear; lia| clear; lia]. apply SVX in MS48; [| clear; lia| clear; lia]. apply SVX in MS56; [| clear; lia| clear; lia]. apply SVX in MS64; [| clear; lia| clear; lia].
  apply SVX in MS72; [| clear; lia| clear; lia]. apply SVX in MS80; [| clear; lia| clear; lia]. apply SVX in MS88; [| clear; lia| clear; lia]. apply SVX in MS96; [| clear; lia| clear; lia].
  apply SVX in MS104; [| clear; lia| clear; lia].
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 8))) as U8. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 9))) as U9.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 18))) as U18. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 19))) as U19.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 20))) as U20. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 21))) as U21.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 22))) as U22. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 23))) as U23.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 24))) as U24. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 25))) as U25.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 26))) as U26. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 27))) as U27. change (bv_modulus 64) with (2 ^ 64) in *.
  pose proof (c_RA L ar HI E X) as (Hr1 & Hr2).
  assert (Ur : 0 <= vr E < 2 ^ 64) by (clear - Hr1; lia).
  assert (Y10 : (65536 + 6840320 <= vfl E \/ vfl E + 1 <= 65536)) by (left; clear - GFLR; lia).
  LeanFeed.pfeed P (PNADP5.adkE2_conc fx2 R2 M2v (fun j => match j with 2%nat => vsp E | 50%nat => vF E | 51%nat => vfl E | 52%nat => ptr | 53%nat => ec
      | 60%nat => vr E | 61%nat => bv_unsigned (getr (vR E) (reg 8)) | 62%nat => bv_unsigned (getr (vR E) (reg 9))
      | 63%nat => bv_unsigned (getr (vR E) (reg 18)) | 64%nat => bv_unsigned (getr (vR E) (reg 19)) | 65%nat => bv_unsigned (getr (vR E) (reg 20))
      | 66%nat => bv_unsigned (getr (vR E) (reg 21)) | 67%nat => bv_unsigned (getr (vR E) (reg 22)) | 68%nat => bv_unsigned (getr (vR E) (reg 23))
      | 69%nat => bv_unsigned (getr (vR E) (reg 24)) | 70%nat => bv_unsigned (getr (vR E) (reg 25)) | 71%nat => bv_unsigned (getr (vR E) (reg 26))
      | 72%nat => bv_unsigned (getr (vR E) (reg 27)) | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0).
  (* [comment removed for export] *)
  pose proof (L5A.ret_to fx3 R3 M3v 0xb4808 W_b30ac (vr E) F_b30ac eq_refl D_b30ac E1 Hr1 Hr2) as MSr.
  assert (MSall : msteps RSEGS (L5SAR.st fx Rc 0xb46b0 MV) (L5SAR.st fx3 R3 (vr E) M3v)).
  { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3| exact MSr]. }
  assert (MGall : mem_grows MV M3v) by (intros x Hx; apply MG3; apply MG12; exact Hx).
  unfold PMSPA.cfg.
  apply (PMAUK.retire_core L ar C HI LYa HIok (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) PNADK.SCR (vsp E - 256) (vsp E - 104) (vsp E) (ocell (vsp E)) (own (vsp E) (vR E) (vr E))
           (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [] XG (W E) [] Mc modelc LKc (vcr E) Ac fx fx3 Rc 0xb46b0 R3 (vr E) M3v (vK E) BI MSall MGall).
  { intros a Ha Nw. unfold PMAUK.Wret in Nw. change (ff_bytes 3) with 512 in Nw. change (512 / 8) with 64 in Nw.
    rewrite FRZ3; [| exact Ha| intros Xa; apply Nw; right; clear - Xa; lia].
    apply AGM2; [exact Ha| intros Y; apply Nw; left; left; exact Y| intros Y; apply Nw; left; right; subst sh; unfold SB; clear - Y; lia]. }
  { exact FL0. }
  intros Mf modelf FZf AHf MRTf AMf HHf. cbn [app] in HHf.
  pose proof BI as (_ & _ & _ & INCAc & INCLc & _).
  assert (AGF : forall a, 0 <= a < 2 ^ 64 -> ~ (vF E <= a < vF E + 8) -> ~ (sh <= a < sh + 64) -> a <> vfl E -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. apply FZf; [exact Ha|]. unfold PMAUK.Wret. change (ff_bytes 3) with 512. change (512 / 8) with 64. intros [[Y|Y]|Y]; [exact (N1 Y)| apply N2; subst sh; unfold SB in Y; clear - Y; lia| exact (N3 Y)]. }
  apply (c_KONT L ar HI E X fx3 R3 Mf modelf LKc Ac ptr).
  - apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    assert (K3 : forall k, In k [3; 4]%nat -> getr R3 (reg k) = getr Rc (reg k)).
    { intros k Hk. rewrite (KS3 k) by (revert k Hk; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K12. revert k Hk. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym (c_Rsp L ar HI E X)) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
         | rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
         | rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
         | rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned | rewrite E26; apply Z_to_bv_bv_unsigned
         | rewrite E27; apply Z_to_bv_bv_unsigned
         | (rewrite (K3 _) by inl; first [exact Q3 | exact Q4]) ] |]).
    destruct Hj.
  - rewrite L5K.rl10. exact E10.
  - exact Hptr.
  - intros i Hi. rewrite AGF; [exact (DF i Hi)| clear - Hi GF1; lia| clear - Hi GFFf; lia| clear - Hi GFSH SHR; lia| clear - Hi GFLf; lia].
  - apply (PNADK.berr_agree Mc Mf _); [| exact ERR]. intros a Ha. apply AGF; [clear - Ha; lia| clear - Ha GFFI; lia| clear - Ha SHR; lia| clear - Ha GFLR; lia].
  - exact AHf.
  - exact MRTf.
  - exact INCLc.
  - exact INCAc.
  - exact AMf.
  - exact HHf.
Qed.

End WithHeap.
End SCFG_1.
End PNADF.
