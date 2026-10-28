(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps BS_InstLaws3 BllocRepX Hoare.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_PcSrc LbB_PcLem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_NBr LbB_NLeaf LbB_NSnp LbB_NKit LbB_NIf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK LbB_PcOvf LbB_PcOvfS LbB_PcXsp LbB_PcXspS LbB_HKit LbB_PqK LbB_Pq LbB_PqS LbB_ContV4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).

Lemma mdef_of_stk : forall m lo hi a n, stk asegs m lo hi -> AIMG_TOP <= lo -> lo <= a -> a + n <= hi -> mdef m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) HI Ha Hn i Hi.
  destruct (S (a + i) ltac:(lia)) as [HV _].
  assert (HX : AIMG_TOP <= bv_unsigned (wa (a + i))) by (unfold wa; rewrite unsigned_lit by lia; lia).
  rewrite (BakeStackRep.wview_high m (wa (a + i)) HX) in HV. exact HV.
Qed.

Lemma canary_any {HCEIL : HeapCeil} : forall m, exists gd, 0 <= gd < 2 ^ 64 /\ CRep.fld asegs m A_CANARY 8 gd.
Proof.
  intros m. destruct (BS_InstLaws3.sspguard_rw_any m) as [g RW].
  exists (bv_unsigned g).
  split; [pose proof (bv_unsigned_in_range 64 g) as K; change (bv_modulus 64) with (2 ^ 64) in K; exact K|].
  apply (LbB_ContV4.fld_of_rw_cells8 m A_CANARY (bv_unsigned g)); [rewrite Z_to_bv_bv_unsigned; exact RW | unfold A_CANARY, BllocRepX.ASSPGUARD; lia].
Qed.

Section NStage.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Hypothesis TDLAW : td_law H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Variables (ENTRY FR : Z) (XOK : Z -> Prop).
  Variable INT : bvmap 5 word -> mem -> Z -> Z -> Z -> Z -> bvmap 5 word -> mem -> Prop.
  Hypothesis HFR : FR = 80 \/ FR = 96.
  Hypothesis EXA : forall (F : bvmap 5 word) (fc : bv 32) R M sp ds xenc fl fill ret lo shi gd,
    npre R M sp ds xenc fl fill ret lo shi gd FR -> XOK xenc ->
    exists nc R1 M1,
      BExec.msteps asegs (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 ENTRY) M (seg_rom asegs))
                         (@PropExec.mkst (PropExec.mkFP F fc) R1 (Z_to_bv 64 AXSP) M1 (seg_rom asegs))
      /\ nmidP R M sp ds FR nc R1 M1 /\ INT R M sp ds ret nc R1 M1.
  Hypothesis EXB : forall (F : bvmap 5 word) (fc : bv 32) R M sp ds xenc fl fill ret lo shi gd nc R1 M1 R' M',
    npre R M sp ds xenc fl fill ret lo shi gd FR -> XOK xenc ->
    INT R M sp ds ret nc R1 M1 -> nback sp ds fl lo shi FR nc R1 M1 R' M' ->
    exists R4 M4,
      BExec.msteps asegs (@PropExec.mkst (PropExec.mkFP F fc) R' (Z_to_bv 64 A_PAD_XS_RET) M' (seg_rom asegs))
                         (@PropExec.mkst (PropExec.mkFP F fc) R4 (Z_to_bv 64 ret) M4 (seg_rom asegs))
      /\ nfin R sp ds ret FR M' R4 M4.

  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
            (s : as_St H) (LB LBk : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
            (ds err len xenc : Z) (DB : list block) (ms : sbuf) (pp hm fl fill : Z).
  Hypothesis PRE : ds_pre H LINV_P5 ENTRY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                         F fc msF m mo s LB DB LF CH (ds_cost (len + 24)) lo B shi errv.
  Hypothesis Ha0 : a0 = Z_to_bv 64 ds.
  Hypothesis Ha1 : a1 = Z_to_bv 64 xenc.
  Hypothesis HX : XOK xenc.
  Hypothesis REPW : ds_rep_w LB m ds err len DB ms pp hm fl fill.
  Hypothesis PERM : Permutation LB (DB ++ LBk).
  Hypothesis DSOB : ds_obj H LF m (bv_unsigned sp) ds DS_SIZE.
  Hypothesis DSIN : obj_inframe LF ds DS_SIZE.
  Hypothesis LEN : len + 24 <= DS_MAXLEN.
  Hypothesis BS : lb_small LB + 2 * 64512 <= RT_SMALL_MAX.
  Hypothesis BL : nlarge LB + 2 <= RT_LARGE_MAX.

  Notation spz := (bv_unsigned sp) (only parsing).
  Let R0 : bvmap 5 word := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  Let ret : Z := bv_unsigned ra.

  Definition NW : list (Z * Z) := [(spz - ADS_STACK, spz); (ds, ds + DS_SIZE)].

  Definition NTD : list (Z * Z) := [(ATDLOC, ATDLOC + 8)].

  Lemma n_nums : AIMG_TOP <= ds /\ ds + DS_SIZE <= lo /\ ds mod 8 = 0 /\ as_FSB H <= ds /\ ds + DS_SIZE <= as_FSB H + AFS_SIZE
                 /\ aceil + ADS_STACK <= spz /\ spz <= 2 ^ 47 /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
                 /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ (ds + DS_SIZE <= ALOWSH_LO \/ AHI_LO <= ds)
                 /\ 0 < ds /\ 0 <= len /\ lo <= spz - ADS_STACK /\ spz <= shi /\ shi <= AAPP_HI /\ spz mod 16 = 0 /\ aceil <= lo.
  Proof.
    destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                     & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
    destruct DSOB as (DSA & DS8 & DSfs & DS0 & DS47 & DSsp & DSO). pose proof DSO as (O1 & O2 & O3).
    destruct (LbB_DCtor.inframe_facts H HH LF m ds DS_SIZE RFS DSIN ltac:(unfold DS_SIZE; lia) O1) as (F1 & _ & F3 & F4).
    destruct (ah_RFS_range H HH LF m RFS) as [(B1 & B2 & B3 & B4) _].
    pose proof aceil_facts as ((A1 & A2) & _ & _). pose proof (stack0_bounds m lo shi S0) as (K1 & K2 & K3).
    pose proof REPW as (DI & _). pose proof (di_len0 _ _ _ _ _ _ _ _ _ _ _ DI) as L0.
    clear - O1 O2 O3 DS8 DS0 F1 F3 F4 B1 B2 A1 A2 K1 K2 K3 LO CEIL SPS L0 SP16.
    unfold ASHADOW_BASE, AHI_LO, AAPP_HI, ADS_STACK, DS_SIZE in *. repeat split; lia.
  Qed.

  Lemma nw_laws : forall LBx LBr m0, as_RFS H LF m0 ->
    Forall (aclient_write_ok H LBx) NW /\ Forall (afs_write_ok H LF) NW /\ Forall stack0_ok NW /\ wins_hi NW /\ Forall aconst_ok NW
    /\ (forall a k, a + k <= AIMG_TOP -> disjoint_from NW a k)
    /\ Forall (LbB_HKit.wmix LBr spz [(ds, ds + DS_SIZE)]) NW.
  Proof.
    intros LBx LBr m0 RFS0.
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    pose proof DSIN as (f & Hf & IF1 & IF2).
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    unfold NW, DS_SIZE, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO, ADS_STACK in *.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. clear - N6. lia.
      + right; right; right; right; left. clear - N4 N5. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold afs_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - N6 N10 A1. lia.
      + right. exists f. split; [exact Hf|]. clear - IF1 IF2. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok, AHI_LO; cbn [fst snd].
      + left. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [right | left]; clear - N11 SH; lia.
    - unfold wins_hi, AIMG_TOP, ALOWSH_LO, AHI_LO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + right. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [left | right]; clear - N1 N11; lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; clear - N1 N11; lia.
    - intros a k Ha. cbn [disjoint_from]. clear - Ha N1 N6 A1. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold LbB_HKit.wmix; cbn [fst snd].
      + left. clear - N6. lia.
      + right; left. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha.
  Qed.

  Lemma n_frame : forall sX LBx DBx (W : Z -> Prop) m0 m1,
    stores_in W m0 m1 -> (forall a, W a -> (spz - ADS_STACK <= a < spz) \/ (ds <= a < ds + DS_SIZE)) ->
    as_RHEAP H sX LBx m0 -> lb_own DBx m0 -> as_RFS H LF m0 -> stk asegs m0 lo spz ->
    (exists e : word, rw_cells asegs m0 (errno_addr tp) [C4 e]) -> as_rauxv_ok H m0 B -> ACONST m0 -> stack0 m0 lo shi ->
    LINV_P5 m0 -> mem_inv asegs m0 -> addressable m0 ds DS_SIZE -> wr_at asegs m0 ds DS_SIZE ->
    munch NW m0 m1 /\ wmono asegs m0 m1
    /\ as_RHEAP H sX LBx m1 /\ lb_own DBx m1 /\ as_RFS H LF m1 /\ stk asegs m1 lo spz
    /\ (exists e : word, rw_cells asegs m1 (errno_addr tp) [C4 e]) /\ as_rauxv_ok H m1 B /\ ACONST m1 /\ stack0 m1 lo shi
    /\ LINV_P5 m1 /\ mem_inv asegs m1 /\ addressable m1 ds DS_SIZE /\ wr_at asegs m1 ds DS_SIZE
    /\ (forall ms0, sb_addr m0 ms0 -> sb_addr m1 ms0).
  Proof.
    intros sX LBx DBx W m0 m1 ST HW RH0 OWN0 RFS0 STK0 (e & ERR0) RAUX0 AC0 S00 LV0 MI0 DSA0 DSW0.
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    destruct (nw_laws LBx [] m0 RFS0) as (WC & WF & WS & WH & WA & WO & _).
    assert (TP : tp = Z_to_bv 64 ATP) by (destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _); exact TP).
    assert (MU : munch NW m0 m1).
    { eapply munch_of_stores_in; [exact ST|]. intros x Hx. unfold NW. cbn [outside fst snd]. destruct (HW x Hx) as [K|K]; clear - K; lia. }
    pose proof (wmono_of_stores_in _ _ _ ST) as WM.
    split; [exact MU|]. split; [exact WM|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH0 | exact MU | exact WM | exact WC]|].
    split; [eapply lb_own_wmono; [exact OWN0 | exact WM]|].
    split; [eapply (ah_RFS_frame H HH); [exact RFS0 | exact MU | exact WM | exact WF]|].
    split.
    { eapply stk_transport; [exact STK0 | exact MU | exact WM |]. intros x Hx. right.
      pose proof STK0 as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HXX : AIMG_TOP <= bv_unsigned (wa x)).
      { unfold wa. rewrite unsigned_lit by (clear - T1 T2 Hx; lia). clear - Hx N18 A1. unfold AIMG_TOP. lia. }
      rewrite (BakeStackRep.wview_high m1 (wa x) HXX) in HV'.
      destruct (m1 (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction]. }
    split.
    { exists e. eapply rw_cells_transport; [exact ERR0 | exact MU | exact WM |].
      cbn [cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia). apply WO. clear. unfold ATP, AIMG_TOP. cbn. lia. }
    split; [eapply (ah_rauxv_frame H HH); [exact RAUX0 | exact MU | exact WM | exact WC]|].
    split; [eapply ACONST_frame; [exact AC0 | exact MU | exact WM | exact WA]|].
    split; [eapply stack0_transport; [exact S00 | exact MU | exact WM | exact WS]|].
    split.
    { eapply LINV_P5_cl; [exact LV0|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by exact Ha.
      apply (disjoint_outside NW a 1); [| clear; lia]. apply WO. unfold aimg_client in Hc. clear - Hc. unfold AIMG_TOP. lia. }
    split.
    { eapply mem_inv_hi; [exact MI0 | exact ST |]. intros a Ha. destruct (HW a Ha) as [K|K]; clear - K N1 N6 A1; unfold AIMG_TOP, ADS_STACK in *; lia. }
    split; [eapply addressable_transport_hi; [exact DSA0 | exact MU | exact WM | clear - N5 N10 A2; unfold AAPP_HI; lia | exact WH]|].
    split; [eapply wr_at_transport; [exact DSW0 | exact WM]|].
    intros ms0 SBA. destruct ms0 as [|d asz]; [exact I|]. cbn [sb_addr] in SBA |- *. destruct SBA as [SA SO]. split; [| exact SO].
    destruct SO as (Q1 & Q2 & Q3). eapply addressable_transport_hi; [exact SA | exact MU | exact WM | exact Q3 | exact WH].
  Qed.

  Lemma n_frame_td : forall sX LBx DBx m0 m1,
    stores_in (zwin ATDLOC (ATDLOC + 8)) m0 m1 -> tdl_pinned m1 ->
    as_RHEAP H sX LBx m0 -> lb_own DBx m0 -> as_RFS H LF m0 -> stk asegs m0 lo spz ->
    (exists e : word, rw_cells asegs m0 (errno_addr tp) [C4 e]) -> as_rauxv_ok H m0 B -> ACONST m0 -> stack0 m0 lo shi ->
    LINV_P5 m0 -> mem_inv asegs m0 -> addressable m0 ds DS_SIZE -> wr_at asegs m0 ds DS_SIZE ->
    as_RHEAP H sX LBx m1 /\ lb_own DBx m1 /\ as_RFS H LF m1 /\ stk asegs m1 lo spz
    /\ (exists e : word, rw_cells asegs m1 (errno_addr tp) [C4 e]) /\ as_rauxv_ok H m1 B /\ ACONST m1 /\ stack0 m1 lo shi
    /\ LINV_P5 m1 /\ mem_inv asegs m1 /\ addressable m1 ds DS_SIZE /\ wr_at asegs m1 ds DS_SIZE
    /\ (forall ms0, sb_addr m0 ms0 -> sb_addr m1 ms0)
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (ATDLOC <= a < ATDLOC + 8) -> m1 (wa a) = m0 (wa a)).
  Proof.
    intros sX LBx DBx m0 m1 ST TD1 RH0 OWN0 RFS0 STK0 (e & ERR0) RAUX0 AC0 S00 LV0 MI0 DSA0 DSW0.
    assert (MU : munch NTD m0 m1).
    { eapply munch_of_stores_in; [exact ST|]. intros x Hx. unfold NTD. cbn [outside fst snd]. unfold zwin in Hx. clear - Hx. lia. }
    pose proof (wmono_of_stores_in _ _ _ ST) as WM.
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    assert (TP : tp = Z_to_bv 64 ATP) by (destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _); exact TP).
    destruct (TDLAW sX LBx LF B m0 m1 MU WM) as (TL1 & TL2 & TL3).
    assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ (ATDLOC <= a < ATDLOC + 8) -> m1 (wa a) = m0 (wa a)).
    { intros a Ha Hn. unfold wa. apply MU. rewrite unsigned_lit by exact Ha. unfold NTD. cbn [outside fst snd]. split; [exact Hn | exact I]. }
    assert (DJ : forall a k, (a + k <= ATDLOC \/ ATDLOC + 8 <= a) -> disjoint_from NTD a k).
    { intros a k Hk. unfold NTD. cbn [disjoint_from fst snd]. split; [clear - Hk; lia | exact I]. }
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    split; [exact (TL1 RH0)|].
    split; [eapply lb_own_wmono; [exact OWN0 | exact WM]|].
    split; [exact (TL2 RFS0)|].
    split.
    { eapply stk_transport; [exact STK0 | exact MU | exact WM |]. intros x Hx. left. unfold NTD. cbn [outside fst snd].
      split; [unfold ATDLOC; clear - Hx N18 A1; lia | exact I]. }
    split.
    { exists e. eapply rw_cells_transport; [exact ERR0 | exact MU | exact WM |].
      cbn [cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia). apply DJ. clear. unfold ATP, ATDLOC. cbn. lia. }
    split; [exact (TL3 RAUX0)|].
    split; [eapply (LbB_NSnp.ACONST_frame_td []); [exact AC0 | exact MU | exact WM | apply Forall_nil]|].
    split.
    { eapply stack0_transport; [exact S00 | exact MU | exact WM |]. unfold NTD. apply Forall_cons; [| apply Forall_nil].
      unfold stack0_ok. right. cbn [fst snd]. unfold ATDLOC. clear - SH. lia. }
    split.
    { destruct LV0 as [RL DT]. split.
      - intros i Hi. rewrite (EQ i ltac:(clear - Hi; lia) ltac:(unfold ATDLOC; clear - Hi; lia)). exact (RL i Hi).
      - apply (dstat_td _ m0 m1 DT ST); [intros a Ha; right; unfold zwin in Ha; exact Ha | exact TD1]. }
    split; [eapply mem_inv_hi; [exact MI0 | exact ST | intros a Ha; unfold zwin, ATDLOC in Ha; clear - Ha; lia]|].
    split.
    { eapply addressable_transport; [exact DSA0 | exact MU | exact WM |]. apply DJ. right.
      unfold sh, ATDLOC. rewrite ASHADOW_BASE_val. clear - N12. Z.div_mod_to_equations. lia. }
    split; [eapply wr_at_transport; [exact DSW0 | exact WM]|].
    split; [| exact EQ].
    intros ms0 SBA. destruct ms0 as [|d asz]; [exact I|]. cbn [sb_addr] in SBA |- *. destruct SBA as [SA SO]. split; [| exact SO].
    destruct SO as (Q1 & Q2 & Q3). eapply addressable_transport; [exact SA | exact MU | exact WM |]. apply DJ. right.
    unfold sh, ATDLOC. rewrite ASHADOW_BASE_val. unfold AIMG_TOP in Q1. clear - Q1. Z.div_mod_to_equations. lia.
  Qed.

  Lemma n_xpres : forall sX LBx DBx m00 m0 m1,
    xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ NTD) m00 m0 -> as_RHEAP H sX LBx m0 -> as_RFS H LF m0 -> Permutation LBx (DBx ++ LBk) ->
    munch NW m0 m1 -> wmono asegs m0 m1 -> xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ NTD) m00 m1.
  Proof.
    intros sX LBx DBx m00 m0 m1 XP RH0 RFS0 PE MU WM.
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    destruct (nw_laws LBx DBx m0 RFS0) as (_ & _ & _ & _ & _ & _ & WX).
    eapply (LbB_HKit.xpres_munch_mixed H HH sX LBx LBk DBx spz _ _ m00 m0 m1 XP RH0); [| | exact MU | exact WM |].
    3: { eapply Forall_impl; [| exact WX]. intros iv [K|[K|K]]; [left; exact K | right; left; intros a Ha; apply rin_ivs_app; left; exact (K a Ha) | right; right; exact K]. }
    - eapply Permutation_trans; [exact PE | apply Permutation_app_comm].
    - clear - N6. unfold ADS_STACK in N6. lia.
  Qed.

  Lemma n_rep : forall sX LBx DBx (W : Z -> Prop) m0 m1 lenx msx ppx hmx fillx,
    ds_rep_w LBx m0 ds err lenx DBx msx ppx hmx fl fillx -> as_RHEAP H sX LBx m0 ->
    stores_in W m0 m1 ->
    (forall a, W a -> (spz - ADS_STACK <= a < spz) \/ (ds + 136 <= a < ds + 144) \/ (ds + 256 <= a < ds + 260) \/ (ATDLOC <= a < ATDLOC + 8)) ->
    CRep.fld asegs m1 (ds + 136) 8 0 -> CRep.fld asegs m1 (ds + 256) 4 32 ->
    addressable m1 ds DS_SIZE -> wr_at asegs m1 ds DS_SIZE -> sb_addr m1 msx ->
    ds_rep_w LBx m1 ds err lenx DBx msx ppx hmx fl 32.
  Proof.
    intros sX LBx DBx W m0 m1 lenx msx ppx hmx fillx (DI0 & BLK0 & DSA0 & DSW0 & DSO0 & SBA0) RH0 ST HW W01 FI1 DSA1 DSW1 SBA1.
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    split; [| split; [exact BLK0 | split; [exact DSA1 | split; [exact DSW1 | split; [exact DSO0 | exact SBA1]]]]].
    eapply (LbB_Pq.ds_inv_reios _ m0 m1); [exact DI0 | right; reflexivity | exact W01 | exact FI1 | |].
    - apply LbB_DRep.mdef_of_wr_at_hi; [exact DSW1 | exact (proj1 DSO0)].
    - intros a Ha HF X1 X2. apply (proj1 ST). rewrite u64_of_Z by exact Ha. intros Wa.
      destruct (HW a Wa) as [K|[K|[K|K]]]; [| exact (X1 K) | exact (X2 K) |].
      2: { destruct HF as [HD | (q & k & Hqk & Hr)].
           - unfold zwin in HD. clear - HD K N1. unfold AIMG_TOP, ATDLOC in *. lia.
           - rewrite (ds_blk_lbl _ _ _ BLK0) in Hqk.
             destruct msx as [|d asz]; cbn [str_blocks] in Hqk; [destruct Hqk|]. destruct Hqk as [Hqk|[]]. injection Hqk. intros <- <-.
             cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
             pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RH0 INb) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP). cbn [blk_addr blk_size fst snd] in Q0, Q16, Qn, QI, QC, QF, QAPP.
             clear - Hr K QI. unfold AIMG_TOP, ATDLOC in *. lia. }
      destruct HF as [HD | (q & k & Hqk & Hr)].
      + unfold zwin in HD. clear - HD K N2 N14. unfold DS_SIZE, ADS_STACK in *. lia.
      + rewrite (ds_blk_lbl _ _ _ BLK0) in Hqk.
        destruct msx as [|d asz]; cbn [str_blocks] in Hqk; [destruct Hqk|]. destruct Hqk as [Hqk|[]]. injection Hqk. intros <- <-.
        cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
        pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RH0 INb) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP). cbn [blk_addr blk_size fst snd] in Q0, Q16, Qn, QI, QC, QF, QAPP.
        clear - Hr K QC N6. unfold ADS_STACK in *. lia.
  Qed.

  Lemma n_pre : exists gd, npre R0 m spz ds xenc fl fill ret lo shi gd FR.
  Proof.
    destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                     & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    pose proof REPW as (DI & BLK & DSA & DSW & DSO & SBA).
    destruct (canary_any m) as (gd & Hgd & FCAN). exists gd.
    destruct DI. destruct di_ios. destruct di_sb.
    unfold DS_SIZE, ADS_STACK, AIMG_TOP, AAPP_HI, NWIN in *. subst R0 ret.
    constructor; unfold NWIN.
    - cbn [PropExec.getr mkR]. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - rewrite Z_to_bv_bv_unsigned. apply Hoare.ret_ok_even. exact RA2.
    - pose proof (bv_unsigned_in_range 64 ra) as K. change (bv_modulus 64) with (2 ^ 64) in K. exact K.
    - cbn [PropExec.getr mkR]. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - cbn [PropExec.getr mkR]. exact TP.
    - cbn [PropExec.getr mkR]. exact Ha0.
    - cbn [PropExec.getr mkR]. exact Ha1.
    - clear - N6 A1 HFR. destruct HFR; lia.
    - clear - N7 N6. lia.
    - exact SP16.
    - eapply (mdef_of_stk m lo (bv_unsigned sp)); [exact STK | clear - CEIL A1; unfold AIMG_TOP; lia | clear - LO HFR; destruct HFR; unfold ADS_STACK in *; lia | clear - HFR; destruct HFR; lia].
    - split; [unfold AIMG_TOP; exact N1|]. split; [exact di_hi | exact di_al].
    - left. clear - N2 N14 HFR. destruct HFR; lia.
    - exact di_def.
    - exact DSO.
    - exact di_vt.
    - exact si_vt.
    - replace (ds + 120) with (ds + 112 + 8) by (clear; lia). exact ii_flags.
    - exact ii_fl.
    - replace (ds + 136) with (ds + 112 + 24) by (clear; lia). exact ii_width.
    - replace (ds + 144) with (ds + 112 + 32) by (clear; lia). exact ii_state.
    - replace (ds + 152) with (ds + 112 + 40) by (clear; lia). exact ii_rdbuf.
    - replace (ds + 160) with (ds + 112 + 48) by (clear; lia). exact ii_loc.
    - replace (ds + 248) with (ds + 112 + 136) by (clear; lia). exact ii_tie.
    - replace (ds + 256) with (ds + 112 + 144) by (clear; lia). exact ii_fill.
    - exact ii_fillr.
    - exact (proj2 LV).
    - exact FCAN.
    - exact Hgd.
    - apply rfull_mkR.
    - split; [exact MI|]. split; [exact AC|]. split; [exact S0|]. apply (proj2 (relro_clear_iff m)). exact (proj1 LV).
    - exact STK.
    - exact CEIL.
    - clear - LO HFR. destruct HFR; unfold ADS_STACK in *; lia.
    - clear - SPS. lia.
  Qed.

  Lemma n_scratch_where : forall LF0 iv, fs_scratch H LF0 iv ->
    (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE) \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE)).
  Proof.
    intros LF0 iv FS.
    destruct FS as [->|(k & ff' & fp' & FF' & E)]; [left; cbn; unfold AFS_FLAGS, AFS_SIZE; lia|].
    pose proof (fresh_frame_facts H _ _ _ _ FF') as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    pose proof (fsz_pos k ltac:(lia)).
    unfold AFS_HDR, AFS_FLAGS in *. destruct E as [E|[E|E]]; rewrite E; cbn [fst snd]; [left; lia | left; unfold AFS_SIZE in *; lia | right].
    assert (sh (as_FSB H) <= sh ff') by (apply sh_mono; lia).
    assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
    assert (sh (ff' + fsz k) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia). lia.
  Qed.

  Lemma n_src : forall m1 p n, stk asegs m1 lo spz -> stack0 m1 lo shi -> as_RFS H LF m1 ->
    spz - FR - 256 <= p -> 0 <= n -> p + n + 64 <= spz ->
    srcx_keep H LBk LF (spz - FR - 256) [(ds, ds + DS_SIZE)] m1 p n.
  Proof.
    intros m1 p n STK1 S01 RFS1 Hp Hn Hpn.
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    assert (FRr : 80 <= FR <= 96) by (clear - HFR; destruct HFR; lia).
    destruct (stk_bytes asegs m1 p (p + n)) as (bs & Lbs & BA).
    { exact (proj1 (stk_split asegs m1 p (p + n) spz (proj2 (stk_split asegs m1 lo p spz STK1 ltac:(clear - Hp N14 FRr Hpn Hn; unfold ADS_STACK in *; lia))) ltac:(clear - Hn Hpn; lia))). }
    { clear - Hn. lia. }
    replace (p + n - p) with n in Lbs by (clear; lia).
    exists bs. split; [exact Lbs|].
    intros m' XS s' LB' AC' MI' FXS XP _ _.
    assert (PHI : p + n <= AAPP_HI) by (unfold AAPP_HI; clear - Hpn N7; lia).
    assert (P0 : 0 <= p) by (clear - Hp N14 N18 A1 FRr; unfold ADS_STACK in *; lia).
    destruct (ah_RFS_range H HH LF m1 RFS1) as [(B1 & B2 & B3 & B4) _].
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    assert (SHF : sh (as_FSB H + AFS_SIZE) <= sh aceil) by (apply sh_mono; clear - N10; lia).
    assert (SHA : sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    assert (SCR : forall iv, In iv XS -> snd iv <= aceil /\ stack0_ok iv).
    { intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FXS iv Hiv) as FS.
      destruct (n_scratch_where LF iv FS) as [[K1 K2]|[K1 K2]].
      - split; [clear - K2 N10; lia|]. unfold stack0_ok, AHI_LO. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in B4.
        destruct B4 as [[_ Q]|[Q _]]; [right | left]; clear - K1 K2 Q SH; lia.
      - split; [clear - K2 SHF SHA; lia|]. unfold stack0_ok. right. clear - K2 SHF. lia. }
    assert (XA : Forall (fun iv : Z * Z => p + n <= fst iv \/ snd iv <= p) ([(ds, ds + DS_SIZE)] ++ XS)).
    { apply Forall_app. split.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. clear - N2 N14 Hp FRr. unfold ADS_STACK in *. lia.
      - apply Forall_forall. intros iv Hiv. right. destruct (SCR iv Hiv) as [K _]. clear - K Hp N14 N18 FRr. unfold ADS_STACK in *. lia. }
    assert (S0' : stack0 m' lo shi).
    { eapply (stack0_xpres H); [exact XP | exact S01 |]. apply Forall_forall. intros iv Hiv.
      apply in_app_or in Hiv. destruct Hiv as [Hiv|Hiv].
      - destruct Hiv as [<-|[]]. unfold stack0_ok, AHI_LO. cbn [fst snd].
        unfold DS_SIZE, ALOWSH_LO, AHI_LO in *. destruct N11 as [K|K]; [right | left]; clear - K SH; lia.
      - exact (proj2 (SCR iv Hiv)). }
    split.
    { eapply xpres_bytes_at; [exact XP | exact BA |]. rewrite Lbs, Z2Nat.id by exact Hn.
      split; [| exact XA]. left. clear - Hp. lia. }
    split.
    { eapply stack0_accessible; [exact S0' | clear - Hp N14 FRr; unfold ADS_STACK in *; lia | exact Hn | clear - Hpn N15; lia]. }
    eapply stack0_shvis; [exact S0' | clear - Hp N14 FRr; unfold ADS_STACK in *; lia | clear - Hn; lia | clear - Hpn N15; lia].
  Qed.

  Lemma np_main : as_SR H (ds_post H LINV_P5 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBk LF [(ds, ds + DS_SIZE); (ATDLOC, ATDLOC + 8)] (ds_cost (len + 24))
                                   lo B shi m mo (Some ds) (ds_op_Q ds_repA0 LB DB ds err (len + 24))) (mkCfg msF mo).
  Proof.
    pose proof PRE as PRE'.
    destruct PRE' as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                      & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
    pose proof n_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18).
    pose proof REPW as (DI0 & BLK0 & DSA0 & DSW0 & DSO0 & SBA0). pose proof (di_len0 _ _ _ _ _ _ _ _ _ _ _ DI0) as LEN0.
    assert (FRr : 80 <= FR <= 96) by (clear - HFR; destruct HFR; lia).
    destruct n_pre as (gd & NP).
    destruct (EXA F fc R0 m spz ds xenc fl fill ret lo shi gd NP HX) as (nc & R1 & M1 & HmsA & NQ & NI1).

    eapply (ahh_evt_then H HH (fun msx => msx = MS R1 F (Z_to_bv 64 AXSP) fc None M1 (seg_rom asegs)) _ s msF _ mo KR VIS).
    { exists (MS R1 F (Z_to_bv 64 AXSP) fc None M1 (seg_rom asegs)). split; [exact HmsA | reflexivity]. }
    intros msF1 mo1 KR1 MP1 E1.
    destruct NQ as [ST1 FFILL X1 X2 X3 X4 X10 X11 X12 Hnc RF1 TD1].
    assert (W1in : forall a, (zwin (spz - (FR + NWIN)) spz a \/ zwin (ds + 256) (ds + 260) a \/ zwin ATDLOC (ATDLOC + 8) a) ->
                     (spz - ADS_STACK <= a < spz) \/ (ds + 136 <= a < ds + 144) \/ (ds + 256 <= a < ds + 260) \/ (ATDLOC <= a < ATDLOC + 8)).
    { intros a [K|[K|K]]; unfold zwin, NWIN, ADS_STACK in *; [left | right; right; left | right; right; right]; clear - K FRr; lia. }

    set (intd := fun a : word => ((ATDLOC <=? bv_unsigned a) && (bv_unsigned a <? ATDLOC + 8))%bool).
    set (Mx := fun a : word => if intd a then M1 a else m a).
    assert (INTD : forall a, intd a = true <-> ATDLOC <= bv_unsigned a < ATDLOC + 8).
    { intros a. subst intd. cbv beta. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. }
    assert (STx : stores_in (zwin ATDLOC (ATDLOC + 8)) m Mx).
    { split.
      - intros a Hn. subst Mx. cbv beta. destruct (intd a) eqn:E; [| reflexivity]. exfalso. apply Hn. unfold zwin. exact (proj1 (INTD a) E).
      - intros a Hd. subst Mx. cbv beta. destruct (intd a) eqn:E; [| exact Hd]. apply (proj2 ST1). exact Hd. }
    assert (TDx : tdl_pinned Mx).
    { intros i Hi. subst Mx. cbv beta.
      assert (E : intd (Z_to_bv 64 (ATDLOC + i)) = true) by (apply (proj2 (INTD _)); rewrite u64_of_Z by (unfold ATDLOC; clear - Hi; lia); clear - Hi; lia).
      rewrite E. exact (TD1 i Hi). }
    assert (ST1x : stores_in (fun a => zwin (spz - (FR + NWIN)) spz a \/ zwin (ds + 256) (ds + 260) a) Mx M1).
    { split.
      - intros a Hn. subst Mx. cbv beta. destruct (intd a) eqn:E; [reflexivity|]. apply (proj1 ST1). intros [K|[K|K]]; [apply Hn; left; exact K | apply Hn; right; exact K |].
        unfold zwin in K. rewrite (proj2 (INTD a) K) in E. discriminate.
      - intros a Hd. subst Mx. cbv beta in Hd. destruct (intd a) eqn:E; [exact Hd | exact (proj2 ST1 a Hd)]. }
    assert (W1in' : forall a, (zwin (spz - (FR + NWIN)) spz a \/ zwin (ds + 256) (ds + 260) a) ->
                     (spz - ADS_STACK <= a < spz) \/ (ds <= a < ds + DS_SIZE)).
    { intros a [K|K]; unfold zwin, NWIN, ADS_STACK, DS_SIZE in *; [left | right]; clear - K FRr; lia. }
    destruct (n_frame_td s LB DB m Mx STx TDx RH OWN RFS STK (ex_intro _ errv ERRN) RAUX AC S0 LV MI DSA0 DSW0)
      as (RHx & OWNx & RFSx & STKx & ERRx & RAUXx & ACx & S0x & LVx & MIx & DSAx & DSWx & SBTx & EQx).
    destruct (n_frame s LB DB _ Mx M1 ST1x W1in' RHx OWNx RFSx STKx ERRx RAUXx ACx S0x LVx MIx DSAx DSWx)
      as (MU1 & WM1 & RH1 & OWN1 & RFS1 & STK1 & (e1 & ERR1) & RAUX1 & AC1 & S01 & LV1 & MI1 & DSA1 & DSW1 & SBT1).
    assert (XPx : xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ NTD) m Mx).
    { intros a Ha [Hc Hnx]. split; [| intros Hw; exact (wmono_of_stores_in _ _ _ STx (wa a) Hw)].
      apply (EQx a Ha). intros K. apply Hnx. apply rin_ivs_app. right. unfold NTD. cbn [rin_ivs fst snd]. left. exact K. }
    pose proof (n_xpres s LB DB m Mx M1 XPx RHx RFSx PERM MU1 WM1) as XP1.
    assert (W0M1 : CRep.fld asegs M1 (ds + 136) 8 0).
    { destruct DI0. destruct di_ios. eapply (fld_via_stores asegs); [exact ST1 | | | | replace (ds + 136) with (ds + 112 + 24) by (clear; lia); exact ii_width].
      - intros y Hy [K|[K|K]]; unfold zwin, NWIN in K; clear - K Hy N1 N2 N14 FRr; unfold DS_SIZE, ADS_STACK, AIMG_TOP, ATDLOC in *; cbn in Hy; lia.
      - clear - N12. lia.
      - clear - N5 N10 A2. unfold DS_SIZE, AFS_SIZE in *. cbn. lia. }
    pose proof (n_rep s LB DB _ m M1 len ms pp hm fill REPW RH ST1 W1in W0M1 FFILL DSA1 DSW1 (SBT1 ms (SBTx ms SBA0))) as REP1.

    rewrite (MS_full_eq R1 F _ fc M1 _ RF1) in E1.
    assert (U2 : bv_unsigned (PropExec.getr R1 2) = spz - FR - 256) by (rewrite X2; apply unsigned_lit; clear - N6 N7 A1 FRr; unfold ADS_STACK in *; lia).
    assert (K4 : PropExec.getr R1 4 = tp) by (rewrite X4; subst R0; reflexivity).
    assert (SRC1 : srcx_keep H LBk LF (spz - FR - 256) [(ds, ds + DS_SIZE)] M1 (spz - FR - 133) nc).
    { apply (n_src M1 (spz - FR - 133) nc STK1 S01 RFS1); clear - Hnc FRr; lia. }

    eapply (ah_seq H HH).
    { eapply ((LbB_PcXspS.xsp_okA H HHbp)
                (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5)
                (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10)
                (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15)
                (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20)
                (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
                (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30)
                (PropExec.getr R1 31) F fc msF1 M1 mo1 s LB LBk DB LF lo B shi e1 ds err len (spz - FR - 133) nc ms pp hm fl 32).
      - unfold pc_pre. split; [exact E1|]. split; [exact RH1|]. split; [exact KR1|]. split; [exact RAUX1|].
        split; [rewrite U2; clear - SPB FRr; lia|]. split; [exact BB|]. split; [rewrite U2; clear - SP16 HFR; destruct HFR as [-> | ->]; Z.div_mod_to_equations; lia|].
        split; [rewrite U2; exact (proj1 (stk_split asegs M1 lo (spz - FR - 256) spz STK1 ltac:(clear - N14 FRr; unfold ADS_STACK in *; lia)))|].
        split; [exact CEIL|]. split; [rewrite U2; clear - N14 FRr; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, ADS_STACK in *; lia|].
        split; [rewrite K4; exact ERR1|]. split; [exact MI1|]. split; [rewrite K4; exact TP|].
        split; [rewrite X1, unsigned_lit by (clear; unfold A_PAD_XS_RET; lia); reflexivity|].
        split; [exact LV1|]. split; [exact AC1|]. split; [exact RFS1|]. split; [exact S01|]. rewrite U2. clear - SPS FRr. lia.
      - exact X10.
      - exact X11.
      - exact X12.
      - clear - Hnc. lia.
      - exact REP1.
      - exact PERM.
      - exact OWN1.
      - split; [exact DSIN | split; [exact DSO0 | split; [exact (di_al _ _ _ _ _ _ _ _ _ _ _ DI0) | exact (di_pos _ _ _ _ _ _ _ _ _ _ _ DI0)]]].
      - rewrite U2. split; [clear - N6 A1 FRr; unfold ADS_STACK in *; lia|]. split; [clear - N7 Hnc FRr; lia|].
        split; [exact SRC1|]. split; [unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI; right; clear - N6 N7 A1 Hnc FRr; unfold ADS_STACK in *; lia|].
        split; [right; clear - FRr; lia|].
        intros a Ha. split; [clear - Ha N2 N14 FRr; unfold DS_SIZE, ADS_STACK in *; lia|].
        intros (b & Hb & Hr). assert (HbL : In b LB) by (eapply Permutation_in; [apply Permutation_sym; exact PERM | apply in_app_iff; left; exact Hb]).
        pose proof (ah_blocks H HH _ _ _ b RH HbL) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        clear - Ha Hr QC N6 FRr. unfold ADS_STACK in *. lia.
      - clear - LEN Hnc. lia.
      - exact BS.
      - exact LBC.
      - exact BL.
      - eapply Z.le_trans; [| exact COST]. unfold ds_cost. clear - Hnc. lia.
      - exact TRok. }
    intros [msF2 mo2] POST2.
    destruct POST2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & e2 & s2x & LB2
                      & VIS2 & KR2 & MP2 & MI2 & STK2 & ERR2 & RAUX2 & RH2 & RFS2 & AC2 & S02 & LV2 & (DB' & ms' & pp' & hm' & PERM2 & REP2 & PP2 & OWN2 & XP2 & AL2)).
    cbn [cfg_ms cfg_model] in *. rewrite U2 in STK2, XP2. rewrite K4 in ERR2.
    assert (RPC : ret_pc (PropExec.getr R1 1) = Z_to_bv 64 A_PAD_XS_RET) by (rewrite X1; unfold A_PAD_XS_RET; apply ret_pc_even; [clear; lia | reflexivity]).
    rewrite RPC in VIS2.
    pose proof REP2 as (DI2 & BLK2 & DSA2 & DSW2 & DSO2 & SBA2).
    assert (PERM' : Permutation LB (LBk ++ DB)) by (eapply Permutation_trans; [exact PERM | apply Permutation_app_comm]).

    assert (XP2k : xpres H LBk (spz - FR - 256) [(ds, ds + DS_SIZE)] M1 m2).
    { destruct ms as [|d asz]; cbn [sbx] in XP2; [exact XP2|].
      cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
      eapply (xpres_drop_blk H HH s LB M1 LBk DB pid d asz (spz - FR - 256) [(ds, ds + DS_SIZE)] M1 m2 RH1 PERM'); [rewrite EDB; left; reflexivity | clear - N6 FRr; unfold ADS_STACK in *; lia |].
      exact XP2. }
    assert (STK2' : stk asegs m2 lo spz).
    { eapply LbB_NBr.stk_join; [exact STK2|]. eapply (LbB_PqS.stk_hi_of_xpres H LBk _ M1 m2); [| exact XP2k |].
      - exact (proj2 (stk_split asegs M1 lo (spz - FR - 256) spz STK1 ltac:(clear - N14 FRr; unfold ADS_STACK in *; lia))).
      - intros a Ha K. cbn [rin_ivs fst snd] in K. clear - Ha K N2 N14 FRr. unfold DS_SIZE, ADS_STACK in *. lia. }
    assert (AGS : agree_on (zwin (spz - FR - 256) spz) M1 m2).
    { intros a Ha. unfold zwin in Ha.
      destruct (XP2k a ltac:(clear - Ha N6 N7 A1 FRr; unfold ADS_STACK in *; lia)) as [E _]; [| exact E].
      split; [left; clear - Ha; lia|]. cbn [rin_ivs fst snd]. clear - Ha N2 N14 FRr. unfold DS_SIZE, ADS_STACK in *. lia. }

    set (R' := mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) u0 u1 u2 (PropExec.getr R1 8) (PropExec.getr R1 9)
                   (Z_to_bv 64 nc) b1 b2 b3 b4 b5 b6 b7 (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21)
                   (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27)
                   u3 u4 u5 u6) in VIS2.
    assert (KP : forall r, In r NKEPT -> PropExec.getr R' r = PropExec.getr R1 r).
    { intros r Hr. subst R'. apply (getr_mkR_keptR R1); [reflexivity | exact Hr]. }
    assert (NB : nback spz ds fl lo shi FR nc R1 M1 R' m2).
    { destruct DI2. destruct di_ios. constructor.
      - exact KP.
      - subst R'. reflexivity.
      - subst R'. apply rfull_mkR.
      - exact AGS.
      - eapply (mdef_of_stk m2 lo spz); [exact STK2' | clear - CEIL A1; unfold AIMG_TOP; lia | clear - N14 FRr; unfold NWIN, ADS_STACK in *; lia | clear - FRr; unfold NWIN; lia].
      - exact di_def.
      - exact di_vt.
      - replace (ds + 120) with (ds + 112 + 8) by (clear; lia). exact ii_flags.
      - replace (ds + 144) with (ds + 112 + 32) by (clear; lia). exact ii_state.
      - replace (ds + 152) with (ds + 112 + 40) by (clear; lia). exact ii_rdbuf.
      - split; [exact MI2|]. split; [exact AC2|]. split; [exact S02|]. apply (proj2 (relro_clear_iff m2)). exact (proj1 LV2). }
    destruct (EXB F fc R0 m spz ds xenc fl fill ret lo shi gd nc R1 M1 R' m2 NP HX NI1 NB) as (R4 & M4 & HmsB & NF).

    eapply (ahh_evt_then H HH (fun msx => msx = MS R4 F (Z_to_bv 64 ret) fc None M4 (seg_rom asegs)) _ s2x msF2 _ mo2 KR2 VIS2).
    { exists (MS R4 F (Z_to_bv 64 ret) fc None M4 (seg_rom asegs)). split; [exact HmsB | reflexivity]. }
    intros msF3 mo3 KR3 MP3 E3.
    apply (ah_done H HH).
    destruct NF as [ST4 W04 V1 V2 V10 VCS RF4].
    assert (W4in : forall a, (zwin (spz - (FR + NWIN)) spz a \/ zwin (ds + 136) (ds + 144) a) ->
                     (spz - ADS_STACK <= a < spz) \/ (ds + 136 <= a < ds + 144) \/ (ds + 256 <= a < ds + 260) \/ (ATDLOC <= a < ATDLOC + 8)).
    { intros a [K|K]; unfold zwin, NWIN, ADS_STACK in *; [left | right; left]; clear - K FRr; lia. }
    assert (W4in' : forall a, (zwin (spz - (FR + NWIN)) spz a \/ zwin (ds + 136) (ds + 144) a) ->
                     (spz - ADS_STACK <= a < spz) \/ (ds <= a < ds + DS_SIZE)).
    { intros a [K|K]; unfold zwin, NWIN, ADS_STACK, DS_SIZE in *; [left | right]; clear - K FRr; lia. }
    destruct (n_frame s2x LB2 DB' _ m2 M4 ST4 W4in' RH2 OWN2 RFS2 STK2' (ex_intro _ e2 ERR2) RAUX2 AC2 S02 LV2 MI2 DSA2 DSW2)
      as (MU4 & WM4 & RH4 & OWN4 & RFS4 & STK4 & (e4 & ERR4) & RAUX4 & AC4 & S04 & LV4 & MI4 & DSA4 & DSW4 & SBT4).
    assert (XPm2 : xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ NTD) m m2).
    { eapply xpres_trans; [exact XP1|]. eapply xpres_weaken; [exact XP2k | clear - FRr; lia | intros b Hb; exact Hb | intros a Ha; apply rin_ivs_app; left; exact Ha]. }
    pose proof (n_xpres s2x LB2 DB' m m2 M4 XPm2 RH2 RFS2 PERM2 MU4 WM4) as XP4.
    assert (FI4 : CRep.fld asegs M4 (ds + 256) 4 32).
    { destruct DI2. destruct di_ios. eapply (fld_via_stores asegs); [exact ST4 | | | | replace (ds + 256) with (ds + 112 + 144) by (clear; lia); exact ii_fill].
      - intros y Hy [K|K]; unfold zwin, NWIN in K; clear - K Hy N2 N14 FRr; unfold DS_SIZE, ADS_STACK in *; cbn in Hy; lia.
      - clear - N12. lia.
      - clear - N5 N10 A2. unfold DS_SIZE, AFS_SIZE in *. cbn. lia. }
    pose proof (n_rep s2x LB2 DB' _ m2 M4 (len + nc) ms' pp' hm' 32 REP2 RH2 ST4 W4in W04 FI4 DSA4 DSW4 (SBT4 ms' SBA2)) as REP4.

    rewrite (MS_full_eq R4 F _ fc M4 _ RF4) in E3.
    assert (G : forall r, In r NCS -> PropExec.getr R4 r = PropExec.getr R0 r) by exact VCS.
    assert (RET : Z_to_bv 64 ret = ret_pc ra).
    { subst ret. rewrite <- (Z_to_bv_bv_unsigned ra) at 2. symmetry. apply ret_pc_even; [| exact RA2].
      pose proof (bv_unsigned_in_range 64 ra) as K. change (bv_modulus 64) with (2 ^ 64) in K. exact K. }
    rewrite RET in E3.
    rewrite (G 3%bv ltac:(unfold NCS; inl)), (G 4%bv ltac:(unfold NCS; inl)), (G 8%bv ltac:(unfold NCS; inl)), (G 9%bv ltac:(unfold NCS; inl)),
            (G 18%bv ltac:(unfold NCS; inl)), (G 19%bv ltac:(unfold NCS; inl)), (G 20%bv ltac:(unfold NCS; inl)), (G 21%bv ltac:(unfold NCS; inl)),
            (G 22%bv ltac:(unfold NCS; inl)), (G 23%bv ltac:(unfold NCS; inl)), (G 24%bv ltac:(unfold NCS; inl)), (G 25%bv ltac:(unfold NCS; inl)),
            (G 26%bv ltac:(unfold NCS; inl)), (G 27%bv ltac:(unfold NCS; inl)) in E3.
    rewrite V1, V2, V10 in E3. subst R0 ret. cbn [PropExec.getr mkR] in E3. rewrite !Z_to_bv_bv_unsigned in E3.

    assert (ALf : as_AL H s2x >= as_AL H s - ds_cost (len + 24)).
    { assert (BK : 8 * (blkof ms' - blkof ms) <= ds_cost (len + 24)).
      { unfold ds_cost. destruct ms' as [|d' asz']; cbn [blkof].
        - destruct ms; cbn [blkof]; [clear - LEN0; lia|].
          cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
          pose proof (ah_blocks H HH _ _ _ (pid, _, _) RH INb) as (_ & _ & Rn & _). cbn [blk_size snd] in Rn. clear - LEN0 Rn. lia.
        - pose proof (di_asz _ _ _ _ _ _ _ _ _ _ _ DI2 d' asz' eq_refl) as AZ.
          destruct ms as [|d asz]; cbn [blkof]; [clear - LEN0 Hnc AZ; lia|].
          cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
          pose proof (ah_blocks H HH _ _ _ (pid, _, _) RH INb) as (_ & _ & Rn & _). cbn [blk_size snd] in Rn. clear - LEN0 Hnc Rn AZ. lia. }
      clear - AL2 BK. lia. }

    unfold ds_post. cbn [cfg_ms cfg_model].
    exists (PropExec.getr R4 5), (PropExec.getr R4 6), (PropExec.getr R4 7), (Z_to_bv 64 ds), (PropExec.getr R4 11), (PropExec.getr R4 12),
           (PropExec.getr R4 13), (PropExec.getr R4 14), (PropExec.getr R4 15), (PropExec.getr R4 16), (PropExec.getr R4 17),
           (PropExec.getr R4 28), (PropExec.getr R4 29), (PropExec.getr R4 30), (PropExec.getr R4 31), M4, e4, s2x, LB2, (@nil (Z * Z)), F, fc.
    split; [exact E3|]. split; [exact FZ|]. split; [intros d Hd; injection Hd; intros <-; reflexivity|].
    split; [exact KR3|]. split; [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2] | exact MP3]|].
    split; [exact MI4|]. split; [exact STK4|]. split; [exact ERR4|]. split; [exact RAUX4|]. split; [exact RH4|].
    split.
    { exists DB'. split; [exists LBk; split; [exact PERM | exact PERM2]|]. split; [| split; [exact OWN4 | exact DSW4]].
      apply ds_repA0_w. exists ms', pp', hm', fl, 32.
      destruct REP4 as (DI4 & R4b). split; [| exact R4b]. eapply LbB_DRep.ds_inv_mono; [exact DI4 | clear - Hnc; lia]. }
    split; [apply Forall_nil|].
    split; [exact XP4|].
    split; [exact RFS4|]. split; [exact AC4|]. split; [exact S04|]. split; [exact LV4 | exact ALf].
  Qed.
End NStage.
