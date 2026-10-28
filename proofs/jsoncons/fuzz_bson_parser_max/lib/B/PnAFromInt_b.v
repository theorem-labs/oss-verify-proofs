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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b
     PnARel3_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDigitFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAFromIntP_b PnAFromIntP2_b PnAFromIntP3_b Ba0_code_b47e0_b47e4_b PnAFromIntK_b PnAFromIntD_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAFI.
Import L5A. Import L5CA. Import L5SAR. Import PNAFIK.
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

(* [comment removed for export] *)
Definition rst (E : fve) (R : bvmap 5 word) : Prop :=
  PNAFID.rbase (vsp E) (vo E) (vF E) R /\ getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) /\ getr R (reg 4) = Z_to_bv 64 (hl_tp L) /\ getr R (reg 27) = getr (vR E) (reg 27).
Lemma rst_keep E R R' : (forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 27]%nat -> getr R' (reg i) = getr R (reg i)) -> rst E R -> rst E R'.
Proof.
  intros KS (RB & R3 & R4 & R27). split; [apply (PNAFID.rbase_keep _ _ _ R R'); [intros i Hi; apply KS; revert i Hi; apply PNAFID.sub_in; vm_compute; reflexivity| exact RB]|].
  split; [rewrite (KS 3%nat) by inl; exact R3|]. split; [rewrite (KS 4%nat) by inl; exact R4| rewrite (KS 27%nat) by inl; exact R27].
Qed.

(* [comment removed for export] *)
Lemma pmem_of E (X : fkc L ar HI E) k Mc modelc LKc Ac : fis L ar HI E k Mc modelc LKc Ac -> PNAFID.pmem (vsp E) (vF E) (vfl E) (mrestrict (ahid Ac modelc) Mc).
Proof.
  intros ST. pose proof (fmem_of L ar C HI LY HIok E X k Mc modelc LKc Ac ST) as (MWS & MFD & MFW & MFSW & MFLC & MFLW & _).
  unfold PNAFID.pmem. unfold SH, SBv in MFSW. repeat split; assumption.
Qed.

Ltac gposeE E X :=
  pose proof (PNAFID.gfacts (vsp E) (vo E) (vF E) (vfl E) (vv E) (c_GEOM L ar HI E X))
    as ((?QS & ?Qo & ?QF & ?Qfl & ?Qv) & ?GS1 & ?GS32 & ?GF1 & ?GF32 & ?GFB & ?GL1 & ?GLB & ?GFL & ?GSF & ?GSL & ?GIF & ?GISF & ?GIL & ?GV).
Ltac pm_open PM := pose proof PM as (?MWS & ?MFD & ?MFW & ?MFSW & ?MFLC & ?MFLW).
Ltac rb_open RB := pose proof RB as (?B2 & ?B8 & ?B9 & ?B18 & ?B19 & ?B20 & ?B23 & ?B24 & ?B25).


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin E (X : fkc L ar HI E) k (fx : FPState) Rc Mc modelc LKc Ac :
  fis L ar HI E k Mc modelc LKc Ac -> rst E Rc -> vn E + 1 <= k <= vn E + 11 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb64dc Mc modelc) (vK E).
Proof.
  intros ST (RB & Q3 & Q4 & Q27) Hk.
  gposeE E X. rb_open RB.
  pose proof (fmem_of L ar C HI LY HIok E X k Mc modelc LKc Ac ST) as (MWS & MFD & MFW & MFSW & MFLC & MFLW & MIMGC & MCSB & MCUAR & MRMS & MOWN & MZS).
  unfold SH, SBv in MFSW, MZS.
  pose proof MOWN as (MS8 & MS16 & MS24 & MS32 & MS40 & MS48 & MS56 & MS64 & MS72 & MS80 & MS88 & MS96).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  pose proof ST as (BI & VS & ZS).
  pose proof (c_G L ar HI E X) as XG. pose proof XG as G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8' GFBIG GF32' GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof (c_GEOM L ar HI E X) as GEO. pose proof (geom_rng _ _ _ _ GEO) as (Eo8 & EF8 & Qo0 & QF0 & Qo1 & QF1 & QoF).
  destruct GEO as (_ & _ & GO1 & GO2 & GO8 & GOB & _ & GF2 & _ & _ & GOF & _ & GL2 & _ & _ & GOL).
  set (sh := vF E / 8 + 2147450880) in *.
  assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296) by (subst sh; clear - QF0 QF1; Lia.lia).
  pose proof (bv_unsigned_in_range 64 (getr Rc (reg 21))) as U21c. change (bv_modulus 64) with (2 ^ 64) in U21c.
  assert (C21 : getr Rc (reg 21) = Z_to_bv 64 (bv_unsigned (getr Rc (reg 21)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  set (cnt := bv_unsigned (getr Rc (reg 21))) in *.
  (let T := type of (PNAFIP.afnT_conc fx Rc MV (PNAFID.VV (vsp E) (vo E) (vF E) (vfl E) (vv E) cnt 0 0)) in let T := eval cbn beta iota delta [PNAFID.VV] in T in LeanFeed.pfeed_at P (PNAFIP.afnT_conc fx Rc MV (PNAFID.VV (vsp E) (vo E) (vF E) (vfl E) (vv E) cnt 0 0)) T ltac:(cbn beta iota delta [PNAFID.VV]) ltac:(L5SAR.sc)).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11 & _).
  assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (vF E <= a < vF E + 8) -> ~ (sh <= a < sh + 64) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha N1 N2. apply FRZ1; [exact Ha| intros Y; apply N1; clear - Y; Lia.lia| intros Y; apply N2; clear - Y; Lia.lia]. }
  assert (AGI1 : forall i, 65536 <= i < 6905856 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi. apply AG1; [clear - Hi; Lia.lia| clear - Hi GF1; Lia.lia| clear - Hi SHR; Lia.lia]. }
  assert (IMGC1 : L5.img_clear M1v 1249280 1282048) by (intros i Hi; rewrite AGI1 by (clear - Hi; Lia.lia); apply MIMGC; exact Hi).
  assert (CSB1 : L5.u64_at RSEGS M1v 1309752 2147450880) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; Lia.lia| clear; Lia.lia| clear; Lia.lia| exact MCSB]).
  assert (CUAR1 : L5.u32_at RSEGS M1v 1309760 1) by (apply (PMF.u32_at_agree RSEGS MV M1v); [intros i Hi; apply AGI1; clear - Hi; Lia.lia| clear; Lia.lia| clear; Lia.lia| exact MCUAR]).
  assert (RMS1 : L5.u64_at RSEGS M1v 1283280 1219844) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; Lia.lia| clear; Lia.lia| clear; Lia.lia| exact MRMS]).
  assert (FSHW1 : L5.writable RSEGS M1v sh 64) by (eapply L5.writable_grows; [exact MG1| exact MFSW]).
  (* [comment removed for export] *)
  destruct (PNAREL.setshadow_f5_run fx1 R1 M1v sh 64 746876 IMGC1 CSB1 CUAR1 RMS1 T10 T11 T1 ltac:(reflexivity) ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) ltac:(clear - SHR; Lia.lia) ltac:(clear - SHR; Lia.lia) FSHW1)
    as (fx2 & R2 & MS2 & KP2).
  set (M2v := wbytes M1v (Z_to_bv 64 sh) (repeat (Z_to_bv 8 245) (Z.to_nat 64))) in *.
  assert (MG2 : mem_grows M1v M2v) by (apply wbytes_grows).
  assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + 64) -> M2v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
  { intros a Ha Hn. subst M2v. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - SHR; Lia.lia). clear - SHR; Lia.lia.
    rewrite repeat_length, !L5.unsigned_lit by (clear - SHR Ha; Lia.lia). clear - Hn. Lia.lia. }
  assert (AGM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (vF E <= a < vF E + 8) -> ~ (sh <= a < sh + 64) -> M2v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha N1 N2. rewrite AG2; [apply AG1; assumption| exact Ha| exact N2]. }
  assert (MG12 : mem_grows MV M2v) by (intros x Hx; apply MG2; apply MG1; exact Hx).
  (* [comment removed for export] *)
  assert (K12 : forall j, In j PNAREL.KEPT -> getr R2 (reg j) = getr Rc (reg j)).
  { intros j Hj. rewrite (KP2 j Hj). apply KS1. revert j Hj. apply (L5K.incl_b PNAREL.KEPT). vm_compute. reflexivity. }
  assert (D2 : getr R2 (reg 2) = Z_to_bv 64 (vsp E - 128)) by (rewrite K12 by inl; exact B2).
  assert (D8 : getr R2 (reg 8) = Z_to_bv 64 (vsp E)) by (rewrite K12 by inl; exact B8).
  assert (D19 : getr R2 (reg 19) = Z_to_bv 64 (vF E)) by (rewrite K12 by inl; exact B19).
  assert (D21 : getr R2 (reg 21) = Z_to_bv 64 cnt) by (rewrite K12 by inl; exact C21).
  assert (WS2 : L5.writable RSEGS M2v (vsp E - 128) 128) by (eapply L5.writable_grows; [exact MG12| exact MWS]).
  assert (FD2 : L5.defined M2v (vF E) 512) by (eapply L5.defined_grows; [exact MG12| exact MFD]).
  assert (FW2 : L5.writable RSEGS M2v (vF E) 512) by (eapply L5.writable_grows; [exact MG12| exact MFW]).
  assert (FSW2 : L5.writable RSEGS M2v sh 64) by (eapply L5.writable_grows; [exact MG12| exact MFSW]).
  assert (FLW2 : L5.writable RSEGS M2v (vfl E) 1) by (eapply L5.writable_grows; [exact MG12| exact MFLW]).
  assert (FLC2 : L5.u64_at RSEGS M2v (vF E + 504) (vfl E)).
  { eapply L5C.u64_at_agree; [intros i Hi; apply AGM2; [clear - Hi GF1; Lia.lia| clear - Hi; Lia.lia| clear - Hi GFB SHR; Lia.lia]| clear - GF1; Lia.lia| clear - GF1; Lia.lia| exact MFLC]. }
  assert (SVX : forall a v, vsp E - 96 <= a -> a + 8 <= vsp E -> L5.u64_at RSEGS MV a v -> L5.u64_at RSEGS M2v a v).
  { intros a v H1 H2 U. eapply L5C.u64_at_agree; [intros i Hi; apply AGM2; [clear - Hi H1 H2 GS1; Lia.lia| clear - Hi H1 H2 GF2; Lia.lia| clear - Hi H1 H2 GS1 SHR; Lia.lia]| clear - H1 GS1; Lia.lia| clear - H2 GS1; Lia.lia| exact U]. }
  apply SVX in MS8; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS16; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS24; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS32; [| clear; Lia.lia| clear; Lia.lia].
  apply SVX in MS40; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS48; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS56; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS64; [| clear; Lia.lia| clear; Lia.lia].
  apply SVX in MS72; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS80; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS88; [| clear; Lia.lia| clear; Lia.lia]. apply SVX in MS96; [| clear; Lia.lia| clear; Lia.lia].
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 8))) as U8. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 9))) as U9.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 18))) as U18. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 19))) as U19.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 20))) as U20. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 21))) as U21.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 22))) as U22. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 23))) as U23.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 24))) as U24. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 25))) as U25.
  pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 26))) as U26. pose proof (bv_unsigned_in_range 64 (getr (vR E) (reg 27))) as U27. change (bv_modulus 64) with (2 ^ 64) in *.
  pose proof (c_RA L ar HI E X) as (Hr1 & Hr2).
  assert (Ur : 0 <= vr E < 2 ^ 64) by (clear - Hr1; Lia.lia).
  clear MWS MFD MFW MFSW MFLC MFLW B2 B8 B9 B18 B19 B20 B23 B24 B25 C21.
  LeanFeed.pfeed P (PNAFIP.afnZ_conc fx2 R2 M2v (fun j => match j with 2%nat => vsp E | 35%nat => cnt | 50%nat => vF E | 51%nat => vfl E
      | 60%nat => vr E | 61%nat => bv_unsigned (getr (vR E) (reg 8)) | 62%nat => bv_unsigned (getr (vR E) (reg 9))
      | 63%nat => bv_unsigned (getr (vR E) (reg 18)) | 64%nat => bv_unsigned (getr (vR E) (reg 19)) | 65%nat => bv_unsigned (getr (vR E) (reg 20))
      | 66%nat => bv_unsigned (getr (vR E) (reg 21)) | 67%nat => bv_unsigned (getr (vR E) (reg 22)) | 68%nat => bv_unsigned (getr (vR E) (reg 23))
      | 69%nat => bv_unsigned (getr (vR E) (reg 24)) | 70%nat => bv_unsigned (getr (vR E) (reg 25)) | 71%nat => bv_unsigned (getr (vR E) (reg 26))
      | 72%nat => bv_unsigned (getr (vR E) (reg 27)) | _ => 0 end)) ltac:(L5SAR.sc).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & FL0).
  (* [comment removed for export] *)
  pose proof (L5A.ret_to fx3 R3 M3v 0xb6694 W_b47e0 (vr E) F_b47e0 eq_refl D_b47e0 E1 Hr1 Hr2) as MSr.
  assert (MSall : msteps RSEGS (L5SAR.st fx Rc 0xb64dc MV) (L5SAR.st fx3 R3 (vr E) M3v)).
  { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3| exact MSr]. }
  assert (MGall : mem_grows MV M3v) by (intros x Hx; apply MG3; apply MG12; exact Hx).
  unfold PMSPA.cfg.
  apply (PMAUK.retire_core L ar C HI LYa HIok (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) PNAFIK.SCR (vsp E - 128) (vsp E - 96) (vsp E) (ocell (vsp E)) (own (vsp E) (vR E) (vr E))
           (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [] XG (W E) [] Mc modelc LKc (vcr E) Ac fx fx3 Rc 0xb64dc R3 (vr E) M3v (vK E) BI MSall MGall).
  { intros a Ha Nw. unfold PMAUK.Wret in Nw. change (ff_bytes 3) with 512 in Nw. change (512 / 8) with 64 in Nw.
    rewrite FRZ3; [| exact Ha| intros Xa; apply Nw; right; clear - Xa; Lia.lia].
    apply AGM2; [exact Ha| intros Y; apply Nw; left; left; exact Y| intros Y; apply Nw; left; right; subst sh; unfold SB; clear - Y; Lia.lia]. }
  { exact FL0. }
  intros Mf modelf FZf AHf MRTf AMf HHf. cbn [app] in HHf.
  pose proof BI as (_ & _ & _ & INCAc & INCLc & _).
  assert (AGF : forall a, 0 <= a < 2 ^ 64 -> ~ (vF E <= a < vF E + 8) -> ~ (sh <= a < sh + 64) -> a <> vfl E -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. apply FZf; [exact Ha|]. unfold PMAUK.Wret. change (ff_bytes 3) with 512. change (512 / 8) with 64. intros [[Y|Y]|Y]; [exact (N1 Y)| apply N2; subst sh; unfold SB in Y; clear - Y; Lia.lia| exact (N3 Y)]. }
  apply (c_KONT L ar HI E X fx3 R3 Mf modelf LKc Ac k).
  - apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    assert (K3 : forall i, In i [3; 4; 27]%nat -> getr R3 (reg i) = getr Rc (reg i)).
    { intros i Hi. rewrite (KS3 i) by (revert i Hi; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply K12. revert i Hi. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity. }
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym (c_Rsp L ar HI E X)) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
         | rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
         | rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
         | rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned | rewrite E26; apply Z_to_bv_bv_unsigned
         | (rewrite (K3 27%nat) by inl; exact Q27)
         | (rewrite (K3 3%nat) by inl; rewrite Q3; exact (eq_sym (c_Rgp L ar HI E X)))
         | (rewrite (K3 4%nat) by inl; rewrite Q4; exact (eq_sym (c_Rtp L ar HI E X))) ] |]).
    destruct Hj.
  - apply (PMFA.vstr_at_agreeA RSEGS Mc Mf (vo E) (PM.VShort k)); [clear - GO1; Lia.lia| clear - GO2 GS1; Lia.lia| | intros c0 n0 p0 E0; discriminate E0| exact VS].
    split.
    + intros i Hi. apply AGF; [clear - Hi GO1 GO2 GS1; Lia.lia| clear - Hi GOF; Lia.lia| clear - Hi GOB SHR; Lia.lia| clear - Hi GOL; Lia.lia].
    + intros x Hx. unfold S, SB.
      assert (Sx : vo E / 8 <= x / 8 < vo E / 8 + 3) by (split; [apply Z.div_le_mono; clear - Hx; Lia.lia| apply Z.div_lt_upper_bound; clear - Hx Eo8; Lia.lia]).
      apply AGF; [clear - Sx Qo0 Qo1; Lia.lia| clear - Sx Qo0 Qo1 GFB; Lia.lia| subst sh; clear - Sx QoF; Lia.lia| clear - Sx Qo0 Qo1 GLB; Lia.lia].
  - exact Hk.
  - exact AHf.
  - exact MRTf.
  - exact INCLc.
  - exact INCAc.
  - exact AMf.
  - exact HHf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shadow_of_digit Fq j : Fq mod 32 = 0 -> 0 <= j <= 9 -> (Fq + 32 + j) / 8 + 2147450880 = Fq / 8 + 2147450880 + 4 + j / 8 /\ 0 <= j / 8 < 2.
Proof.
  intros F32 Hj. pose proof (div8 Fq (mod32_8 Fq F32)) as E8.
  assert (E : (Fq + 32 + j) / 8 = Fq / 8 + 4 + j / 8).
  { replace (Fq + 32 + j) with ((Fq / 8 + 4) * 8 + j) by (clear - E8; Lia.lia). rewrite Z.div_add_l by (clear; Lia.lia). reflexivity. }
  split; [rewrite E; clear; Lia.lia|]. split; [apply Z.div_pos; clear - Hj; Lia.lia| apply Z.div_lt_upper_bound; clear - Hj; Lia.lia].
Qed.

Lemma push_round E (X : fkc L ar HI E) (PB : PNRAa.str_push_back_short_spec L ar HI) (fx : FPState) R Mc modelc LKc Ac (j k : Z) :
  fis L ar HI E k Mc modelc LKc Ac -> rst E R -> 0 <= j <= 9 -> k <= 21 ->
  getr R (reg 22) = Z_to_bv 64 (vF E + 32 + j) -> getr R (reg 26) = Z_to_bv 64 (vF E + 32 + j) ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
      fis L ar HI E (k + 1) M3 model3 LK3 Aw3 -> rst E R2 -> getr R2 (reg 21) = getr R (reg 21) ->
      getr R2 (reg 22) = Z_to_bv 64 (vF E + 32 + j) -> getr R2 (reg 26) = Z_to_bv 64 (vF E + 32 + j) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xb64bc M3 model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb64a0 Mc modelc) (vK E).
Proof.
  intros ST RS Hj Hk G22 G26 KR. pose proof RS as (RB & Q3 & Q4 & _).
  gposeE E X. rb_open RB.
  pose proof (fmem_of L ar C HI LY HIok E X k Mc modelc LKc Ac ST) as (MWS & MFD & MFW & MFSW & MFLC & MFLW & _ & _ & _ & _ & _ & MZS).
  unfold SH, SBv in MFSW, MZS.
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  destruct (shadow_of_digit (vF E) j GF32 Hj) as (ESH & HJ8).
  assert (ZD : L5KA.zeros_at MV ((vF E + 32 + j) / 8 + 2147450880) 1).
  { rewrite ESH. apply (L5KA.zeros_at_sub MV _ 2 _ 1 MZS); clear - HJ8; Lia.lia. }
  assert (Hj64 : 0 <= j < 2 ^ 64) by (clear - Hj; Lia.lia).
  (let T := type of (PNAFIP.afnQB_conc fx R MV (PNAFID.VV (vsp E) (vo E) (vF E) (vfl E) (vv E) 0 0 j)) in let T := eval cbn beta iota delta [PNAFID.VV] in T in LeanFeed.pfeed_at P (PNAFIP.afnQB_conc fx R MV (PNAFID.VV (vsp E) (vo E) (vF E) (vfl E) (vv E) 0 0 j)) T ltac:(cbn beta iota delta [PNAFID.VV]) ltac:(L5SAR.sc)).
  destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & B1 & B10).
  assert (EM : M1 = MV) by (apply functional_extensionality; exact FR1). subst M1.
  apply (fk_ro L ar C HI LY HIok E X k fx fx1 R R1 0xb64a0 0xd5bc4 Mc modelc LKc Ac ST MS1).
  intros model3 ST3 _.
  change 0xd5bc4 with (PNL.pn_str_push_back PMA.AN).
  apply (fk_call_pb L ar C HI HIok E X k fx1 R1 Mc model3 LKc Ac 0xb64bc PB ST3 Hk B1 ltac:(clear; unfold L5.ra_ok; Lia.lia)).
  { rewrite (KS1 2%nat) by inl. exact B2. } { rewrite (KS1 3%nat) by inl. exact Q3. } { rewrite (KS1 4%nat) by inl. exact Q4. } { exact B10. }
  intros fx2 R2 M3 model4 LK3 Aw3 RP2 ST4.
  assert (R12 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R (reg i)).
  { intros i Hi. rewrite (L5SAR.cs_of_preserved R1 R2 i RP2 Hi). apply KS1. revert i Hi. apply PNAFID.sub_in. vm_compute. reflexivity. }
  apply (KR fx2 R2 M3 model4 LK3 Aw3 ST4).
  - apply (rst_keep E R R2); [intros i Hi; apply R12; revert i Hi; apply PNAFID.sub_in; vm_compute; reflexivity| exact RS].
  - apply R12. inl.
  - rewrite (R12 22%nat) by inl. exact G22.
  - rewrite (R12 26%nat) by inl. exact G26.
Qed.

(* [comment removed for export] *)
Lemma push_loop E (X : fkc L ar HI E) (PB : PNRAa.str_push_back_short_spec L ar HI) (jn : nat) :
  forall (fx : FPState) R Mc modelc LKc Ac (j k : Z),
  j = Z.of_nat jn -> fis L ar HI E k Mc modelc LKc Ac -> rst E R -> j <= 9 ->
  getr R (reg 22) = Z_to_bv 64 (vF E + 32 + j) -> getr R (reg 26) = Z_to_bv 64 (vF E + 32 + j) ->
  vn E <= k -> k + j + 1 <= vn E + 11 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb64a0 Mc modelc) (vK E).
Proof.
  pose proof (c_N L ar HI E X) as HN.
  induction jn as [|jn IH]; intros fx R Mc modelc LKc Ac j k Ej ST RS Hj G22 G26 Hnk Hkj;
    apply (push_round E X PB fx R Mc modelc LKc Ac j k ST RS ltac:(clear - Ej Hj; Lia.lia) ltac:(clear - Ej Hkj HN; Lia.lia) G22 G26);
    intros fx2 R2 M3 model3 LK3 Aw3 ST3 RS3 _ E22 E26;
    pose proof RS3 as (RB3 & Q3 & Q4 & _); gposeE E X; rb_open RB3;
    pose proof (pmem_of E X (k + 1) M3 model3 LK3 Aw3 ST3) as PM3; pm_open PM3;
    set (MV := mrestrict (ahid Aw3 model3) M3) in *;
    (assert (Hj64 : 0 <= j < 2 ^ 64) by (clear - Ej Hj; Lia.lia));
    pose proof (PNAFIP.afnQR_conc fx2 R2 MV (PNAFID.VV (vsp E) (vo E) (vF E) (vfl E) (vv E) 0 0 j)) as P; cbn beta iota delta [PNAFID.VV] in P;
    L5SAR.feed P ltac:(L5SAR.sc);
    destruct P as (fx3 & R3 & M4 & MG4 & FR4 & _ & EX);
    (assert (EM : M4 = MV) by (apply functional_extensionality; exact FR4)); subst M4.
  - (* [comment removed for export] *)
    destruct EX as [(MS3 & KS3 & _ & _ & CT)|(MS3 & KS3 & _)].
    { exfalso. subst j. rewrite Z.add_0_l in CT. rewrite !Z.mod_small in CT by (clear - GF1; Lia.lia). clear - CT. Lia.lia. }
    apply (fk_ro L ar C HI LY HIok E X (k + 1) fx2 fx3 R2 R3 0xb64bc 0xb64dc M3 model3 LK3 Aw3 ST3 MS3).
    intros model4 ST4 _.
    apply (fin E X (k + 1) fx3 R3 M3 model4 LK3 Aw3 ST4).
    + apply (rst_keep E R2 R3); [intros i Hi; apply KS3; revert i Hi; apply PNAFID.sub_in; vm_compute; reflexivity| exact RS3].
    + subst j. clear - Hnk Hkj. Lia.lia.
  - (* [comment removed for export] *)
    destruct EX as [(MS3 & KS3 & C22 & C26 & _)|(MS3 & KS3 & _ & _ & CT)].
    2: { exfalso. rewrite !Z.mod_small in CT by (clear - GF1 Ej Hj; Lia.lia). clear - CT Ej. Lia.lia. }
    apply (fk_ro L ar C HI LY HIok E X (k + 1) fx2 fx3 R2 R3 0xb64bc 0xb64a0 M3 model3 LK3 Aw3 ST3 MS3).
    intros model4 ST4 _.
    apply (IH fx3 R3 M3 model4 LK3 Aw3 (Z.of_nat jn) (k + 1) eq_refl ST4).
    + apply (rst_keep E R2 R3); [intros i Hi; apply KS3; revert i Hi; apply PNAFID.sub_in; vm_compute; reflexivity| exact RS3].
    + clear - Ej Hj. Lia.lia.
    + rewrite C22. f_equal. clear - Ej. Lia.lia.
    + rewrite C26. f_equal. clear - Ej. Lia.lia.
    + clear - Hnk. Lia.lia.
    + clear - Ej Hkj. Lia.lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_pos E (X : fkc L ar HI E) (PB : PNRAa.str_push_back_short_spec L ar HI) (fx : FPState) R Mc modelc LKc Ac (d : Z) :
  fis L ar HI E (vn E) Mc modelc LKc Ac -> rst E R -> 1 <= d <= 10 ->
  getr R (reg 22) = Z_to_bv 64 (vF E + 32 + (d - 1)) -> getr R (reg 26) = Z_to_bv 64 (vF E + 32 + (d - 1)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb64a0 Mc modelc) (vK E).
Proof.
  intros ST RS Hd G22 G26.
  apply (push_loop E X PB (Z.to_nat (d - 1)) fx R Mc modelc LKc Ac (d - 1) (vn E)); [clear - Hd; Lia.lia| exact ST| exact RS| clear - Hd; Lia.lia| exact G22| exact G26| clear; Lia.lia| clear - Hd; Lia.lia].
Qed.

Lemma after_neg E (X : fkc L ar HI E) (PB : PNRAa.str_push_back_short_spec L ar HI) (fx : FPState) R Mc modelc LKc Ac (d : Z) :
  fis L ar HI E (vn E) Mc modelc LKc Ac -> rst E R -> 1 <= d <= 10 ->
  getr R (reg 1) = Z_to_bv 64 0xb6488 -> getr R (reg 10) = Z_to_bv 64 (vo E) -> getr R (reg 21) = Z_to_bv 64 d -> getr R (reg 26) = Z_to_bv 64 (vF E + 32 + d) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5bc4 Mc modelc) (vK E).
Proof.
  intros ST RS Hd G1 G10 G21 G26. pose proof RS as (RB & Q3 & Q4 & _). pose proof (c_N L ar HI E X) as HN.
  change 0xd5bc4 with (PNL.pn_str_push_back PMA.AN).
  apply (fk_call_pb L ar C HI HIok E X (vn E) fx R Mc modelc LKc Ac 0xb6488 PB ST ltac:(clear - HN; Lia.lia) G1 ltac:(clear; unfold L5.ra_ok; Lia.lia)).
  { exact (proj1 RB). } { exact Q3. } { exact Q4. } { exact G10. }
  intros fx2 R2 M3 model3 LK3 Aw3 RP2 ST3.
  assert (R12 : forall i, In i L5SAR.cs_all -> getr R2 (reg i) = getr R (reg i)) by (intros i Hi; exact (L5SAR.cs_of_preserved R R2 i RP2 Hi)).
  assert (RS2 : rst E R2) by (apply (rst_keep E R R2); [intros i Hi; apply R12; revert i Hi; apply PNAFID.sub_in; vm_compute; reflexivity| exact RS]).
  pose proof RS2 as (RB2 & _). gposeE E X. rb_open RB2.
  pose proof (pmem_of E X (vn E + 1) M3 model3 LK3 Aw3 ST3) as PM3. pm_open PM3.
  set (MV := mrestrict (ahid Aw3 model3) M3) in *.
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; Lia.lia).
  assert (C21 : getr R2 (reg 21) = Z_to_bv 64 d) by (rewrite (R12 21%nat) by inl; exact G21).
  assert (C26 : getr R2 (reg 26) = Z_to_bv 64 (vF E + 32 + d)) by (rewrite (R12 26%nat) by inl; exact G26).
  (let T := type of (PNAFIP.afnR1_conc fx2 R2 MV (PNAFID.VV (vsp E) (vo E) (vF E) (vfl E) (vv E) d 0 0)) in let T := eval cbn beta iota delta [PNAFID.VV] in T in LeanFeed.pfeed_at P (PNAFIP.afnR1_conc fx2 R2 MV (PNAFID.VV (vsp E) (vo E) (vF E) (vfl E) (vv E) d 0 0)) T ltac:(cbn beta iota delta [PNAFID.VV]) ltac:(L5SAR.sc)).
  destruct P as (fx3 & R3 & M4 & MG4 & FR4 & _ & MS3 & KS3 & _ & E22 & E26).
  assert (EM : M4 = MV) by (apply functional_extensionality; exact FR4). subst M4.
  apply (fk_ro L ar C HI LY HIok E X (vn E + 1) fx2 fx3 R2 R3 0xb6488 0xb64a0 M3 model3 LK3 Aw3 ST3 MS3).
  intros model4 ST4 _.
  apply (push_loop E X PB (Z.to_nat (d - 1)) fx3 R3 M3 model4 LK3 Aw3 (d - 1) (vn E + 1)); [clear - Hd; Lia.lia| exact ST4| | clear - Hd; Lia.lia| | | clear; Lia.lia| clear - Hd; Lia.lia].
  - apply (rst_keep E R2 R3); [intros i Hi; apply KS3; revert i Hi; apply PNAFID.sub_in; vm_compute; reflexivity| exact RS2].
  - rewrite E22. f_equal. clear. Lia.lia.
  - rewrite E26. f_equal. clear. Lia.lia.
Qed.

(* [comment removed for export] *)
Theorem from_int_ok : PNRAa.str_push_back_short_spec L ar HI -> PNRAa.from_int_spec L ar HI.
Proof.
  intros PB. unfold PNRAa.from_int_spec, PNRA.from_int_spec.
  intros fx R M model K LB FF LK Aw cr o v sp r n HH AM K0 ENT FRM FRS SP32 A10 Hv A11 AO O8 VS Hn KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 2) with 16384 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL, FSIMG.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO O8) as AOB.
  assert (OFg : forall sp' scr', (6905856 <= o /\ o + 24 <= ahl_ceil ar /\ o + 24 <= 2 ^ 47 /\ o mod 8 = 0 /\ (o / 8) * 8 = o)
                /\ (2147446784 + 17592186048512 <= o \/ o + 24 <= 2147446784)
                /\ (forall i, 0 <= i < 24 -> aclient L ar LB FF sp' scr' (o + i))
                /\ (forall i, 0 <= i < 24 / 8 -> aclient L ar LB FF sp' scr' (o / 8 + SB + i))).
  { intros sp' scr'. pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model o 24 sp' scr' HH AOB ltac:(clear; Lia.lia) ltac:(reflexivity)) as (Y1 & Y2 & _ & _ & _ & Y3 & Y4).
    split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
  destruct (OFg sp 16384) as ((O1 & O2 & O3 & O4 & O5) & OBIG & OCL & OSCL). change (24 / 8) with 3 in OSCL.
  pose proof (L5ADHR.statics_vis L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (IMGC & CSB & CUAR).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 16384 128 HH ASTK ltac:(clear; Lia.lia)) as (SL128 & SH128 & SWR).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  assert (QA : 0 <= sp < 2 ^ 64 /\ 0 <= o < 2 ^ 64 /\ 140735332487296 <= sp <= 140737488355328) by (clear - SL128 SHI SPT SLO O1 O3; Lia.lia).
  destruct QA as (QAs & QAo & QS).
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(clear; Lia.lia)) as Qv.
  assert (A10m : getr R (reg 10) = Z_to_bv 64 (v mod 2 ^ 64)) by (rewrite PNAFID.to_bv_mod; exact A10).
  LeanFeed.pfeed P (PNAFIP.afnA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v mod 2 ^ 64 | _ => 0 end)) ltac:(first [assumption | unfold PNAFIP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T22 & T24
                 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
  unfold PMSPA.cfg. change (PNL.pn_from_int PMA.AN) with 0xb6200.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb6200 R1 0x5df30 M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros Y; clear - Y Wa QS; Lia.lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL128 SHI SPT; Lia.lia| intros Y; clear - Y; Lia.lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 16384 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 16384 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; Lia.lia.
    - clear - Xa Y SL128; Lia.lia. }
  assert (EK01 : L5SAR.ek L ar LB FF sp 16384 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 16384 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ Y. apply (NCS0 a); [clear - Y; Lia.lia| exact Hc]. }
  assert (DK01 : L5SAR.dk L ar LB FF sp 16384 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  assert (SV1 : forall a w, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a w -> L5.u64_at RSEGS M1 a w).
  { intros a w Ha1 Ha2 Y. apply (proj1 (L5A.u64_at_vis H M1 a w (VISs a 8 ltac:(clear - Ha1 SL128 SPT; Lia.lia) ltac:(clear - Ha2 SHI SPT; Lia.lia)) ltac:(clear - Ha1 SL128 SPT; Lia.lia) ltac:(clear - Ha2 SHI SPT; Lia.lia))).
    rewrite VIS1. exact Y. }
  assert (U1 : bv_unsigned (getr R (reg 1)) = r) by (rewrite Rra; apply L5.unsigned_lit; clear - Hr1; Lia.lia).
  rewrite U1 in C8.
  assert (OWN1 : own sp R r M1).
  { unfold own, saves. repeat split; (apply SV1; [clear; Lia.lia| clear; Lia.lia| assumption]). }
  clear C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk3 : ff_room 3 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 2 FF LK 3 FRM); [clear; Lia.lia| right; right; left; reflexivity]).
  change 0x5df30 with (PMA.SM_PC 3).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 3 LB [] FF LK cr Aw sp 16384 (sp - 128) (sp - 96) sp (ocell sp) (own sp R r)
           fx1 R1 M M1 model model1 K 0xb6270 ltac:(right; right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; Lia.lia. }
  { replace (sp - 128) with (sp + (-8) * 16) by (clear; Lia.lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; Lia.lia. } { clear; Lia.lia. } { clear; Lia.lia. } { clear; Lia.lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R r Ma Mb ltac:(clear - SL128 SPT; Lia.lia) ltac:(clear - SHI SPT; Lia.lia) OW AG). }
  { exact FRk3. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; Lia.lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12 DK12 AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. change (512 - 8) with 504 in *. cbn [app] in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. cbn [app] in GHH2.
  assert (HH2 : ri_inv HI LB ((F, 3, sp - 128 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 3, sp - 128 + 32) :: FF) in *.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 16384 128 HH2 ASTK2 ltac:(clear; Lia.lia)) as (_ & _ & SWR2).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 HH2) as (_ & VISs2 & _).
  (* [comment removed for export] *)
  destruct (OFg 0 0) as (_ & _ & OCL0 & _).
  destruct (APART o 24 0 0 OCL0 ltac:(clear; Lia.lia)) as (ApF & ApSF & ApFL).
  assert (GEOM : geom sp o F fl).
  { unfold geom.
    split; [exact QS|]. split; [exact SP32|]. split; [exact O1|]. split; [clear - O2 SLO; Lia.lia|]. split; [exact O4|]. split; [exact OBIG|].
    split; [clear - GFR; Lia.lia|]. split; [clear - GFCEIL SLO; Lia.lia|]. split; [exact GF32|]. split; [exact GFBIG|]. split; [exact ApF|].
    split; [clear - GFLR; Lia.lia|]. split; [clear - GFLR SLO; Lia.lia|]. split; [exact GFLBIG|]. split; [exact GFLA|]. exact ApFL. }
  pose proof (geom_rng _ _ _ _ GEOM) as (Eo8 & EF8 & Qo0 & QF0 & Qo1 & QF1 & QoF).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 o) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B22R : getr R2 (reg 22) = Z_to_bv 64 v) by (rewrite (R2c 22%nat) by inl; rewrite T22; apply PNAFID.to_bv_mod).
  assert (B24R : getr R2 (reg 24) = Z_to_bv 64 2147450880) by (rewrite (R2c 24%nat) by inl; exact T24).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (B3R : getr R2 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD)) by (rewrite (R2c 3%nat) by inl; rewrite (KS1 3%nat) by inl; exact Rgp).
  assert (B4R : getr R2 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (R2c 4%nat) by inl; rewrite (KS1 4%nat) by inl; exact Rtp).
  assert (PM2 : PNAFID.pmem sp F fl MV2).
  { unfold PNAFID.pmem. split; [exact SWR2|]. split; [exact FDEF|]. split; [exact FW|]. split; [exact FSHW|].
    split; [replace (F + 504) with (F + 512 - 8) by (clear; Lia.lia); exact FLC| exact FLW]. }
  destruct (PNAFID.digits sp o F fl v GEOM Hv fx1 R2 MV2 B2R B8R B9R B10R B20R B22R B24R PM2)
    as (fx3 & R3 & M3v & d & MG3 & FRZ3 & Hd & RB3 & K34 & ZS3 & PM3 & EX).
  assert (EX' : exists pc3, msteps RSEGS (L5SAR.st fx1 R2 0xb6270 MV2) (L5SAR.st fx3 R3 pc3 M3v)
            /\ ( (0 <= v /\ pc3 = 0xb64a0 /\ getr R3 (reg 22) = Z_to_bv 64 (F + 32 + (d - 1)) /\ getr R3 (reg 26) = Z_to_bv 64 (F + 32 + (d - 1)))
              \/ (v < 0 /\ pc3 = 0xd5bc4 /\ getr R3 (reg 1) = Z_to_bv 64 0xb6488 /\ getr R3 (reg 10) = Z_to_bv 64 o
                  /\ getr R3 (reg 21) = Z_to_bv 64 d /\ getr R3 (reg 26) = Z_to_bv 64 (F + 32 + d)) )).
  { destruct EX as [(Y1 & Y2 & _ & Y4 & Y5)|(Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
    - exists 0xb64a0. split; [exact Y2|]. left. split; [exact Y1|]. split; [reflexivity|]. split; [exact Y4| exact Y5].
    - exists 0xd5bc4. split; [exact Y2|]. right. split; [exact Y1|]. split; [reflexivity|]. split; [exact Y3|]. split; [exact Y4|]. split; [exact Y5| exact Y6]. }
  clear EX. destruct EX' as (pc3 & MS3 & EX).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb6270 R3 pc3 M3v (PNAFID.Wd sp F) K HH2 AM2 MS3 MG3 FRZ3).
  { intros a Ha Wa. unfold PNAFID.Wd in Wa. split.
    - destruct Wa as [Y|[Y|[Y|Y]]].
      + unfold aclientw, aclient_g. right; left. split; [clear - Y SL128 SHI SPT; Lia.lia| intros Z0; clear - Z0; Lia.lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; clear - Y; Lia.lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; clear - Y; Lia.lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Y; Lia.lia.
    - destruct Wa as [Y|[Y|[Y|Y]]]; [clear - Y QS; Lia.lia| clear - Y GFR; Lia.lia| clear - Y GFR; Lia.lia| clear - Y QF0; Lia.lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (WdC : forall a, PNAFID.Wd sp F a -> (sp - 128 <= a < sp - 96) \/ (F <= a < F + 512) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64)).
  { intros a [Y|[Y|[Y|Y]]]; [left; clear - Y; Lia.lia| right; left; clear - Y; Lia.lia| right; left; clear - Y; Lia.lia| right; right; exact Y]. }
  assert (EK23 : L5SAR.ek L ar LB FF sp 16384 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 16384 [] M2 M3 (PNAFID.Wd sp F) FR3). intros a Ha Hc _ Wa. destruct (WdC a Wa) as [Y|[Y|Y]].
    - apply (NCS0 a); [clear - Y; Lia.lia| exact Hc].
    - destruct (APART a 1 sp 16384 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; Lia.lia); exact Hc) ltac:(clear; Lia.lia)) as (Z0 & _). clear - Y Z0; Lia.lia.
    - destruct (APART a 1 sp 16384 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; Lia.lia); exact Hc) ltac:(clear; Lia.lia)) as (_ & Z0 & _). unfold SB in Z0. clear - Y Z0; Lia.lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 16384 [] M M2 M3 EK02 EK23) as EK03.
  assert (OWN3 : own sp R r M3).
  { apply (own_agree sp R r M1 M3 ltac:(clear - SL128 SPT; Lia.lia) ltac:(clear - SHI SPT; Lia.lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; Lia.lia| clear - Ha SL128 SHI SPT; Lia.lia|].
    intros Wa. destruct (WdC a Wa) as [Y|[Y|Y]]; [clear - Y Ha; Lia.lia| clear - Y Ha GFCEIL SLO; Lia.lia| clear - Y Ha QF1 QS; Lia.lia]. }
  set (E := FVE R r sp o v n LB FF LK Aw cr model M K F fl LK2 M2 model2).
  assert (DK03 : L5SAR.dk L ar LB FF sp 16384 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 16384 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3).
  assert (BI3 : PMAUK.binv L ar HI M model LB FF LK Aw sp 16384 (sp - 128) (own sp R r) F 3 (W E) [] M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. cbn [app]. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 16384 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LB FF sp 16384 (W E) [] M M3 EK03); intros a _ r0 []|].
    split; [exact DK03|].
    split; [exact OWN3|].
    change (ff_bytes 3 / 8) with 64. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 64 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  (* [comment removed for export] *)
  assert (AGS : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 16384 a -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc. apply EK03. split; [exact Ha|]. split; [exact Hc| intros r0 []]. }
  assert (VS3 : PM.vstr_at RSEGS PMSPA.accA M3 o (PM.VShort n)).
  { apply (PMFA.vstr_at_agreeA RSEGS M M3 o (PM.VShort n)); [clear - O1; Lia.lia| clear - O3; Lia.lia| | intros c0 n0 p0 E0; discriminate E0| exact VS].
    split.
    - intros i Hi. apply AGS; [clear - Hi O1 O3; Lia.lia|]. replace i with (o + (i - o)) by (clear; Lia.lia). apply OCL. clear - Hi; Lia.lia.
    - intros x Hx. unfold S.
      assert (Sx : o / 8 <= x / 8 < o / 8 + 3) by (split; [apply Z.div_le_mono; clear - Hx; Lia.lia| apply Z.div_lt_upper_bound; clear - Hx Eo8; Lia.lia]).
      apply AGS; [unfold SB; clear - Sx Qo0 Qo1; Lia.lia|]. replace (x / 8 + SB) with (o / 8 + SB + (x / 8 - o / 8)) by (clear; Lia.lia). apply OSCL. clear - Sx; Lia.lia. }
  assert (ZSf : L5KA.zeros_at M3 (SH F + 4) 2).
  { unfold SH, SBv. apply (proj1 (L5A.zeros_at_vis H2 M3 (F / 8 + 2147450880 + 4) 2 (L5A.avis_sub H2 _ _ (F / 8 + 2147450880 + 4) 2 VSH ltac:(unfold SB; clear; Lia.lia) ltac:(unfold SB; clear; Lia.lia)))).
    rewrite VIS3. exact ZS3. }
  assert (XC : fkc L ar HI E).
  { constructor; cbn [vR vr vsp vo vv vn vLB vFF vLK vAw vcr vmodel vM vK vF vfl vLK2 vM2 vmodel2 E]; unfold PNAFIK.SCR;
      first [ exact GEOM | exact G | exact HH | exact K0 | exact Rra | exact RAok | exact Rsp | exact Rgp | exact Rtp | exact ASTK | exact STKSH | exact FRM | exact FRS | exact AO | exact Hn | exact Hv | idtac ].
    unfold PNAFIK.kont. cbn [vR vr vsp vo vv vn vLB vFF vLK vAw vcr vmodel vM vK vF vfl vLK2 vM2 vmodel2 E]. unfold PNAFIK.SCR, PNAFIK.W. cbn [vo E]. exact KONT. }
  assert (ST3 : fis L ar HI E (vn E) M3 model3 LK2 Aw).
  { unfold fis. cbn [vR vr vsp vo vv vn vLB vFF vLK vAw vcr vmodel vM vK vF vfl vLK2 vM2 vmodel2 E]. unfold PNAFIK.SCR.
    split; [exact BI3|]. split; [exact VS3| exact ZSf]. }
  assert (RS3 : rst E R3).
  { split; [exact RB3|]. cbn [vR vr vsp vo vv vn vLB vFF vLK vAw vcr vmodel vM vK vF vfl vLK2 vM2 vmodel2 E].
    split; [rewrite (K34 3%nat) by inl; exact B3R|]. split; [rewrite (K34 4%nat) by inl; exact B4R| rewrite (K34 27%nat) by inl; rewrite (R2c 27%nat) by inl; rewrite (KS1 27%nat) by inl; reflexivity]. }
  destruct EX as [(Hv0 & -> & E22 & E26)|(Hvn & -> & E1 & E10 & E21 & E27)].
  - exact (after_pos E XC PB fx3 R3 M3 model3 LK2 Aw d ST3 RS3 Hd E22 E26).
  - exact (after_neg E XC PB fx3 R3 M3 model3 LK2 Aw d ST3 RS3 Hd E1 E10 E21 E27).
Qed.

End WithHeap.
End SCFG_1.
End PNAFI.
