(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMState BMem BCells BArr BExec BLFrame BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BakeStackRep BllocRepX RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_Conv LbB_Call LbB_DStat LbB_NBr LbB_NMc LbB_NLeaf LbB_NPc1 LbB_NLoops LbB_NPc2 LbB_NPc3 LbB_NSn LbB_NVf LbB_NPfc.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DPdK LbB_PqK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumWalkTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac NumLeaf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).
Local Ltac xms H := first [exact H | apply msteps_bridge; exact H].

Definition AVFPRINTF_STUB : Z := 0xa36c4.
Definition IVF_PFC_RA : Z := 0xa8398.
Definition IVF_REAL_RA : Z := 0xa83b0.
Definition IVF_RETPC : Z := 0xa83c4.
Definition IVF_FRAME : Z := 2320.

Lemma kw_cells_hd : forall E M A c cs v (w : nat), rw_cells asegs M A (c :: cs) -> csize c = w -> (1 <= w <= 8)%nat ->
  cbytes c = word_to_le_bytes w (Z_to_bv 64 v) -> 0 <= A -> A + 8 <= 2 ^ 64 ->
  kentry_ok SEGS E M (KWord (SA (ELit 0) A) w (ELit v)).
Proof.
  intros E M A c cs v w RW Hw Hw8 Hb H0 H1. eapply (kword_of_rw_cells asegs E M A _ 0 c); [exact RW | reflexivity | exact Hw | exact Hw8 | | lia | cbn; lia | cbn [edenot]; exact Hb].
  unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. lia.
Qed.
Lemma w2lb1 : forall v, word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. discriminate. Qed.

Section Ivf.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variable gd : Z.
  Hypothesis Hgd : 0 <= gd < 2 ^ 64.
  Variables (R : bvmap 5 word) (M : mem) (f ret v conv lo shi : Z).
  Hypothesis Hra : getr R 1%bv = Z_to_bv 64 ret.
  Hypothesis Hret : ret_ok (Z_to_bv 64 ret).
  Hypothesis Hretr : 0 <= ret < 2 ^ 64.
  Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 f.
  Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 f.
  Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 (f + 2640).
  Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 (f + 2512).
  Hypothesis Hflo : 2 ^ 33 <= f - IVF_FRAME.
  Hypothesis Hfhi : f + 2644 < 2 ^ 47.
  Hypothesis Hal : f mod 16 = 0.
  Hypothesis HD : mdef M (f - IVF_FRAME) (IVF_FRAME + 2644).
  Hypothesis Fv : fld SEGS M (f + 2512) 8 v.
  Hypothesis Hv : 0 <= v < 2 ^ 64.
  Hypothesis F0 : fld SEGS M (f + 2640) 1 37.
  Hypothesis F1 : fld SEGS M (f + 2641) 1 108.
  Hypothesis F2 : fld SEGS M (f + 2642) 1 conv.
  Hypothesis F3 : fld SEGS M (f + 2643) 1 0.
  Hypothesis Hconv : conv = 117 \/ conv = 100 \/ conv = 120.
  Hypothesis Hvpos : conv = 100 -> v < 2 ^ 63.
  Hypothesis Gflags : fld SEGS M f 4 0.
  Hypothesis Gwrite : fld SEGS M (f + 72) 8 A_SN_WRITE_A.
  Hypothesis Gbuf : fld SEGS M (f + 88) 8 (f + 255).
  Hypothesis Gbsz : fld SEGS M (f + 96) 8 0.
  Hypothesis Gmode : fld SEGS M (f + 136) 4 0.
  Hypothesis Glock : fld SEGS M (f + 140) 4 (2 ^ 32 - 1).
  Hypothesis Glbf : fld SEGS M (f + 144) 4 (2 ^ 32 - 1).
  Hypothesis Gcookie : fld SEGS M (f + 152) 8 (f + 232).
  Hypothesis Gcs : fld SEGS M (f + 232) 8 (f + 2616).
  Hypothesis Gcn : fld SEGS M (f + 240) 8 23.
  Hypothesis FCAN : fld SEGS M A_CANARY 8 gd.

  Hypothesis RF : rfull R.
  Hypothesis NI : ninv lo shi M.
  Hypothesis STK : stk asegs M lo f.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LOS : lo + AINTRIN_STACK + 1088 <= f.
  Hypothesis SHI : f + 2708 <= shi.

  Definition ivf_post (nc : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
    getr R' 10%bv = Z_to_bv 64 nc /\ 1 <= nc <= 21
    /\ (forall r, In r leaf_kept -> getr R' r = getr R r)
    /\ stores_in (fun a => zwin (f - 1024 - AINTRIN_STACK) (f + 248) a \/ zwin (f + 2616) (f + 2616 + nc + 1) a) M M'
    /\ rfull R' /\ ninv lo shi M' /\ stk asegs M' lo f.

  Lemma vfprintf_icpt : exists nc R' M',
    BExec.msteps SEGS (@mkst (PropExec.mkFP F fc) R (Z_to_bv 64 AVFPRINTF_STUB) M (seg_rom SEGS)) (@mkst (PropExec.mkFP F fc) R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
    /\ ivf_post nc R' M'.
  Proof.
    unfold IVF_FRAME in *.
    pose proof NI as (MI & AC & S0 & RRC). pose proof aceil_facts as ((AF1 & AF2) & _). pose proof (stack0_bounds M lo shi S0) as (B1 & B2 & B3).
    pose proof (ACONST_drv_flags M AC) as (CCHK & _ & _ & _ & _ & CINI & _). pose proof (ACONST_drv_reals M AC) as (_ & _ & _ & _ & CVFP & _).
    pose proof (ACONST_cell M AGOT_CFLAGS [C8 (wz 0x222b68)] AC ltac:(cbn; tauto)) as CGOT.

    set (E := Eseed R (@nil word)).
    assert (HR : regs_ok E (srs sr_id [(10%bv : reg, EVar 2); (11%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2640)); (12%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2512))]) R) by srs_ok.
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-2320)) (ELit 2320); KRange (EVar 2) (2 ^ 33 + 2320) (2 ^ 47 - 2644); KAlign (EVar 2) 16;
       KWord (SA (ELit 0) AINITED_CELL) 1 (ELit 1);
       KWord (SA (ELit 0) AGOT_CFLAGS) 8 (ELit 0x222b68); KWord (SA (ELit 0) ACF_CHKPRINTF_CELL) 1 (ELit 1);
       KImg 0x10000 0x17e000; KImg 0x17e000 0x186000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ f (-2320) 2320); [evs; exact Hsp | lia | lia | lia | lia | eapply mdef_sub; [exact HD | lia | lia]].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal].
      - eapply kw_cells_hd; [exact CINI | reflexivity | cbn; lia | symmetry; apply w2lb1 | unfold AINITED_CELL; lia | unfold AINITED_CELL; lia].
      - eapply kw_cells_hd; [exact CGOT | reflexivity | cbn; lia | reflexivity | unfold AGOT_CFLAGS; lia | unfold AGOT_CFLAGS; lia].
      - eapply kw_cells_hd; [exact CCHK | reflexivity | cbn; lia | symmetry; apply w2lb1 | unfold ACF_CHKPRINTF_CELL; lia | unfold ACF_CHKPRINTF_CELL; lia].
      - apply kimg_ro. exact MI. - apply kimg_relro. exact RRC. }
    xrun_at HR HK (PropExec.mkFP F fc) AVFPRINTF_STUB (seg_rom SEGS) 100%nat [APRINTF_COMMON; A_VFPRINTF; IVF_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1. wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
    assert (ST1 : stores_in (zwin (f - 64) f) M M1) by (subst M1; stores_tower).
    assert (SV1 : slots SEGS M1 f [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; Z_to_bv 64 (f + 2512)]) by (subst M1; slots_tower).
    assert (T01 : forall a (n : nat) x, (a + Z.of_nat n <= f - 64 \/ f <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M1 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    regval HR1 (1%bv : reg) IVF_PFC_RA X1. regval HR1 (2%bv : reg) (f - 48) X2. regval HR1 (11%bv : reg) (f + 2640) X11.
    regval HR1 (8%bv : reg) (f + 2640) X8. regval HR1 (9%bv : reg) f X9.
    assert (RF1 : rfull R1) by exact (msteps_full asegs _ _ Hms1 RF).
    assert (NI1 : ninv lo shi M1) by (eapply (ninv_keep lo shi M M1 _ NI ST1); intros a Ha; unfold zwin in Ha; clear - Ha CEIL LOS Hfhi AF1; unfold AINTRIN_STACK in *; lia).
    pose proof NI1 as (MI1 & AC1 & S01 & RR1).
    assert (F0' : fld SEGS M1 (f + 2640) 1 37) by (apply T01; [cbn; lia | lia | cbn; lia | exact F0]).
    assert (F1' : fld SEGS M1 (f + 2640 + 1) 1 108) by (replace (f + 2640 + 1) with (f + 2641) by lia; apply T01; [cbn; lia | lia | cbn; lia | exact F1]).
    assert (F2' : fld SEGS M1 (f + 2640 + 2) 1 conv) by (replace (f + 2640 + 2) with (f + 2642) by lia; apply T01; [cbn; lia | lia | cbn; lia | exact F2]).
    assert (F3' : fld SEGS M1 (f + 2640 + 3) 1 0) by (replace (f + 2640 + 3) with (f + 2643) by lia; apply T01; [cbn; lia | lia | cbn; lia | exact F3]).

    destruct (@printf_common_l _ (PropExec.mkFP F fc) R1 M1 (f - 48) IVF_PFC_RA (f + 2640) conv lo shi X1 ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(unfold IVF_PFC_RA; lia)
                X2 X11 ltac:(unfold PFC_FRAME; lia) ltac:(lia) ltac:(mlia)
                ltac:(unfold PFC_FRAME; eapply stores_in_mdef; [exact ST1 | eapply mdef_sub; [exact HD | lia | lia]]) ltac:(lia) ltac:(unfold PFC_FRAME; right; lia)
                F0' F1' F2' F3' Hconv
                MI1 RR1 AC1 S01 ltac:(clear - LOS; unfold AINTRIN_STACK in *; lia) ltac:(clear - SHI; lia) ltac:(unfold PFC_FRAME; clear - LOS; unfold AINTRIN_STACK in *; lia))
      as (R2 & M2 & Hms2 & K2 & ST2).
    unfold PFC_FRAME in ST2.
    assert (ST02 : stores_in (zwin (f - 2320) f) M M2).
    { eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact ST2 | ..]; intros a Ha; unfold zwin in *; lia. }
    assert (T02 : forall a (n : nat) x, (a + Z.of_nat n <= f - 2320 \/ f <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST02 | intros y Hy; unfold zwin; lia | lia | lia | exact HF]. }
    assert (SV2 : slots SEGS M2 f [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; Z_to_bv 64 (f + 2512)]).
    { eapply slots_agree; [exact SV1 | cbn; lia | lia |]. eapply stores_in_agree; [exact ST2|]. intros b Hb. unfold zwin in *. cbn in Hb. lia. }
    assert (RF2 : rfull R2) by exact (msteps_full asegs _ _ Hms2 RF1).
    assert (NI2 : ninv lo shi M2) by (eapply (ninv_keep lo shi M1 M2 _ NI1 ST2); intros a Ha; unfold zwin in Ha; clear - Ha CEIL LOS Hfhi AF1; unfold AINTRIN_STACK in *; lia).
    pose proof NI2 as (MI2 & AC2 & S02 & RR2).

    assert (Y2 : getr R2 2%bv = Z_to_bv 64 (f - 48)) by (rewrite (K2 2%bv) by inl; exact X2).
    assert (Y8 : getr R2 8%bv = Z_to_bv 64 (f + 2640)) by (rewrite (K2 8%bv) by inl; exact X8).
    assert (Y9 : getr R2 9%bv = Z_to_bv 64 f) by (rewrite (K2 9%bv) by inl; exact X9).
    set (E2 := Eseed R2 (@nil word)).
    assert (HR2 : regs_ok E2 (srs sr_id [(8%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2688)); (9%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 48))]) R2) by srs_ok.
    assert (HK2 : know_ok SEGS E2 M2
      [KRange (EVar 2) (2 ^ 33 + 2272) (2 ^ 47 - 2692);
       KWord (SA (EVar 2) 8) (N.to_nat 8) (EAlu ALU_ADD (EVar 2) (ELit 2560));
       KWord (SA (ELit 0) AVFPRINTFP_CELL) 8 (ELit AREAL_VFPRINTF);
       KImg 0x10000 0x17e000; KImg 0x17e000 0x186000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - krv Y2.
      - kwe (SV2 4%nat ltac:(cbn [length]; lia)) Y2.
      - pose proof (ACONST_drv_reals M2 AC2) as (_ & _ & _ & _ & CVFP2 & _).
        eapply kw_cells_hd; [exact CVFP2 | reflexivity | cbn; lia | reflexivity | unfold AVFPRINTFP_CELL; lia | unfold AVFPRINTFP_CELL; lia].
      - apply kimg_ro. exact MI2. - apply kimg_relro. exact RR2. }
    xrun_at HR2 HK2 (PropExec.mkFP F fc) IVF_PFC_RA (seg_rom SEGS) 40%nat [APRINTF_COMMON; A_VFPRINTF; IVF_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK2. rename R' into R3. rename HR' into HR3. rename Hms into Hms3.
    regval HR3 (1%bv : reg) IVF_REAL_RA Z1. regval HR3 (2%bv : reg) (f - 48) Z2. regval HR3 (10%bv : reg) f Z10.
    regval HR3 (11%bv : reg) (f + 2640) Z11. regval HR3 (12%bv : reg) (f + 2512) Z12.
    assert (RF3 : rfull R3) by exact (msteps_full asegs _ _ Hms3 RF2).
    assert (STK2 : stk asegs M2 lo (f - 48)).
    { eapply LbB_PqK.stk_keep; [exact (proj1 (stk_split asegs M lo (f - 48) f STK ltac:(clear - LOS; unfold AINTRIN_STACK in *; lia)))
        | eapply (munch_of_stores_in _ [(f - 2320, f)]); [exact ST02 | intros x Hx; cbn [outside fst snd]; unfold zwin in Hx; clear - Hx; lia]
        | exact (wmono_of_stores_in _ _ _ ST02) | clear - CEIL AF1; unfold AIMG_TOP; lia]. }

    pose proof (vfprintf_sn H HH F fc gd Hgd R3 M2 f IVF_REAL_RA v conv lo shi) as LV.
    repeat lazymatch type of LV with (exists _, _) => fail | forall _ : ?T, _ =>
      specialize (LV ltac:(first [eassumption | reflexivity | apply bv_eq; vm_compute; reflexivity | unfold IVF_REAL_RA; lia
                                  | eapply mdef_sub; [eapply stores_in_mdef; [exact ST02 | exact HD] | lia | lia]
                                  | apply T02; [cbn; lia | lia | cbn; lia | assumption]
                                  | eapply (fld_via_stores SEGS); [exact ST02 | intros y Hy; unfold zwin, A_CANARY, ASSPGUARD in *; lia | unfold A_CANARY, ASSPGUARD; lia | unfold A_CANARY, ASSPGUARD; cbn; lia | exact FCAN]
                                  | clear - LOS; unfold AINTRIN_STACK in *; lia | clear - SHI; lia])) end.
    destruct LV as (nc & R4 & M4 & Hms4 & P10 & Pnc & PK & PST & RF4 & NI4 & STK4).

    assert (SV4 : slots SEGS M4 f [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; Z_to_bv 64 (f + 2512)]).
    { eapply slots_agree; [exact SV2 | cbn; lia | lia |]. eapply stores_in_agree; [exact PST|]. intros b Hb. cbv beta. unfold zwin, AINTRIN_STACK in *. cbn in Hb. lia. }
    assert (W2 : getr R4 2%bv = Z_to_bv 64 (f - 48)) by (rewrite (PK 2%bv) by inl; exact Z2).
    set (E4 := Eseed R4 [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv]).
    assert (HR4 : regs_ok E4 sr_id R4) by (apply regs_ok_seed).
    assert (HK4 : know_ok SEGS E4 M4
      [KRange (EVar 2) (2 ^ 33 + 2272) (2 ^ 47 - 2692);
       KWord (SA (EVar 2) 40) (N.to_nat 8) (EVar 32); KWord (SA (EVar 2) 32) (N.to_nat 8) (EVar 33);
       KWord (SA (EVar 2) 24) (N.to_nat 8) (EVar 34); KWord (SA (EVar 2) 16) (N.to_nat 8) (EVar 35)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - krv W2.
      - kwe (SV4 0%nat ltac:(cbn [length]; lia)) W2. - kwe (SV4 1%nat ltac:(cbn [length]; lia)) W2.
      - kwe (SV4 2%nat ltac:(cbn [length]; lia)) W2. - kwe (SV4 3%nat ltac:(cbn [length]; lia)) W2. }
    xrun_at HR4 HK4 (PropExec.mkFP F fc) IVF_REAL_RA (seg_rom SEGS) 40%nat [APRINTF_COMMON; A_VFPRINTF; IVF_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK4. rename R' into R5. rename HR' into HR5. rename Hms into Hms5.
    regval HR5 (1%bv : reg) ret T1.
    pose proof (@ret_at (PropExec.mkFP F fc) SEGS IVF_RETPC R5 M4 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) T1 Hret) as Hms6.
    exists nc, R5, M4. split.
    { eapply BExec.msteps_trans; [xms Hms1|]. eapply BExec.msteps_trans; [xms Hms2|]. eapply BExec.msteps_trans; [xms Hms3|].
      eapply BExec.msteps_trans; [xms Hms4|]. eapply BExec.msteps_trans; [xms Hms5 | xms Hms6]. }
    split; [regval HR5 (10%bv : reg) nc T10; exact T10 |].
    split; [exact Pnc|].
    split.
    { intros r Hr. unfold leaf_kept in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR5 PK HR3 K2 HR1|]). destruct Hr. }
    assert (ST04 : stores_in (fun a => zwin (f - 1024 - AINTRIN_STACK) (f + 248) a \/ zwin (f + 2616) (f + 2616 + nc + 1) a) M M4).
    { eapply (stores_in_join _ _ _ M M2 M4); [exact ST02 | exact PST | ..]; intros a Ha; cbv beta in *; unfold zwin, AINTRIN_STACK in *; lia. }
    split; [exact ST04|]. split; [exact (msteps_full asegs _ _ Hms5 RF4)|]. split; [exact NI4|].
    eapply LbB_PqK.stk_keep; [exact STK
      | eapply (munch_of_stores_in _ [(f - 1024 - AINTRIN_STACK, f + 248); (f + 2616, f + 2616 + nc + 1)]); [exact ST04 | intros x Hx; cbv beta in Hx; cbn [outside fst snd]; unfold zwin in Hx; clear - Hx; lia]
      | exact (wmono_of_stores_in _ _ _ ST04) | clear - CEIL AF1; unfold AIMG_TOP; lia].
  Qed.
End Ivf.
