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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_PcSrc LbB_PcLem LbB_PqK LbB_PqK2 LbB_PqR LbB_Pq.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK LbB_PcOvf LbB_PcOvfS LbB_PcXsp LbB_PcXspS LbB_HKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma pq_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 APQ_RET) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  unfold APQ_RET. step. apply evt_done. exact HQ.
Qed.

Lemma srcx_keep_LF {HCEIL : HeapCeil} : forall (H : asr) LBk LF LF' spz X m p n,
  srcx_keep H LBk LF spz X m p n -> (forall f, In f LF -> In f LF') -> srcx_keep H LBk LF' spz X m p n.
Proof.
  intros H LBk LF LF' spz X m p n (bs & L & K) SUB. exists bs. split; [exact L|].
  intros m' XS s' LB' AC MI FX XP RH INC. apply (K m' XS s' LB'); [exact AC | exact MI | | exact XP | exact RH | exact INC].
  apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as Fi.
  destruct Fi as [Fi|(k & ff & fp & (FR & FO & FF) & E)]; [left; exact Fi | right]. exists k, ff, fp. split; [| exact E].
  split; [exact FR|]. split; [exact FO|]. intros f Hf. apply FF. apply SUB. exact Hf.
Qed.

Lemma stk_join : forall mm lo' mid hi, stk asegs mm lo' mid -> stk asegs mm mid hi -> stk asegs mm lo' hi.
Proof.
  intros mm lo' mid hi (A1 & A2 & A3) (B1 & B2 & B3). split; [exact A1|]. split; [exact B2|].
  intros a Ha. destruct (Z.lt_ge_cases a mid); [apply A3 | apply B3]; lia.
Qed.

Lemma stk_hi_of_xpres {HCEIL : HeapCeil} : forall (H : asr) LBx X m1 m2 mid hi,
  stk asegs m1 mid hi -> xpres H LBx mid X m1 m2 -> (forall a, mid <= a < hi -> ~ rin_ivs X a) -> stk asegs m2 mid hi.
Proof.
  intros H LBx X m1 m2 mid hi (S1 & S2 & S3) XP HX. split; [exact S1|]. split; [exact S2|].
  intros a Ha. destruct (S3 a Ha) as [W1 [b R1]].
  destruct (XP a ltac:(lia) (conj (or_introl (proj1 Ha)) (HX a Ha))) as [E WV].
  split; [exact (WV W1)|]. exists b. unfold mrd in *. rewrite E. exact R1.
Qed.

Section PQS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
            (s : as_St H) (LB LBk : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
            (ds err len p n : Z) (DB : list block) (ms : sbuf) (pp hm fl fill : Z).
  Hypothesis PRE : ds_pre H LINV_P5 APUT_CSEQ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                         F fc msF m mo s LB DB LF CH (ds_cost (len + n)) lo B shi errv.
  Hypothesis Ha0 : a0 = Z_to_bv 64 ds.
  Hypothesis Ha1 : a1 = Z_to_bv 64 p.
  Hypothesis Ha2 : a2 = Z_to_bv 64 n.
  Hypothesis REPW : ds_rep_w LB m ds err len DB ms pp hm fl fill.
  Hypothesis PERM : Permutation LB (DB ++ LBk).
  Hypothesis DSOB : ds_obj H LF m (bv_unsigned sp) ds DS_SIZE.
  Hypothesis DSIN : obj_inframe LF ds DS_SIZE.
  Hypothesis N0 : 0 <= n.
  Hypothesis P0 : 0 < p \/ n = 0.
  Hypothesis SRCK : srcx_keep H LBk LF (bv_unsigned sp) [(ds, ds + DS_SIZE)] m p n.
  Hypothesis IAM : in_app_mem p (p + n).
  Hypothesis PSTK : p + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= p.
  Hypothesis PDJ : forall a, p <= a < p + n -> ~ (ds <= a < ds + DS_SIZE) /\ ~ in_block DB a.
  Hypothesis LEN : len + n <= DS_MAXLEN.
  Hypothesis BS : lb_small LB + 2 * 64512 <= RT_SMALL_MAX.
  Hypothesis BL : nlarge LB + 2 <= RT_LARGE_MAX.

  Notation spz := (bv_unsigned sp) (only parsing).
  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Lemma pq_ctx_ok : pq_ctx H sp tp a0 a1 a2 m ds p n len err lo LF LB DB ms pp hm fl fill s.
  Proof.
    destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                     & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
    destruct DSOB as (DSA & DS8 & DSfs & DS0 & DS47 & DSsp & DSO).
    destruct (LbB_DCtor.inframe_facts H HH LF m ds DS_SIZE RFS DSIN ltac:(unfold DS_SIZE; clear; lia) (proj1 DSO)) as (DSH & DSV & _ & _).
    pose proof (stack0_bounds m lo shi S0) as SB.
    pose proof REPW as (DI & _). pose proof (di_len0 _ _ _ _ _ _ _ _ _ _ _ DI) as L0.
    constructor; try assumption.
    - unfold in_app_mem, AAPP_HI, AHI_LO, ASHADOW_BASE, DS_MAXLEN in *. clear - IAM N0 LEN L0. lia.
    - clear - SB SPS. lia.
    - clear - LFn. unfold DS_FRAMES in LFn. eapply Nat.le_trans; [| exact LFn]. apply (proj1 (Nat.add_le_mono_l _ _ _)). repeat constructor.
  Qed.

  Notation CTX := pq_ctx_ok (only parsing).
  Notation WBq ff1 fp1 ff2 fp2 := (LbB_Pq.WB H sp ds ff1 fp1 ff2 fp2) (only parsing).
  Notation WCq ff1 fp1 spa ff2 fp2 := (LbB_Pq.WC sp ds ff1 fp1 spa ff2 fp2) (only parsing).
  Notation nums2q := (LbB_Pq.nums2 H HHbp sp tp a0 a1 a2 m ds p n len err lo LF LB DB ms pp hm fl fill s CTX) (only parsing).
  Notation djs2q := (LbB_Pq.djs2 H sp ds p n lo fl) (only parsing).
  Notation fr_placeq := (LbB_Pq.fr_place H sp tp a0 a1 a2 m ds p n len err lo LF LB DB ms pp hm fl fill s CTX) (only parsing).
  Notation PQARGS := (fun X => X H HHbp ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ds p n len err lo LF LB DB ms pp hm fl fill s CTX) (only parsing).

  Definition XSq (ff1 fp1 ff2 fp2 : Z) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + AFS_FLAGS); (fp1, fp1 + 1); (ff1, ff1 + fsz 1); (sh ff1, sh ff1 + fshn 1);
     (fp2, fp2 + 1); (ff2, ff2 + fsz 1); (sh ff2, sh ff2 + fshn 1)].

  Lemma xsq_scratch : forall ff1 fp1 ff2 fp2, fresh_frame H LF 1 ff1 fp1 -> fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    Forall (fs_scratch H LF) (XSq ff1 fp1 ff2 fp2).
  Proof.
    intros ff1 fp1 ff2 fp2 FR1 FR2.
    assert (FR2' : fresh_frame H LF 1 ff2 fp2).
    { destruct FR2 as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|]. intros f Hf. apply A3. right. exact Hf. }
    pose proof (fs_scratch_of_fresh H LF 1 ff1 fp1 FR1) as S1. pose proof (fs_scratch_of_fresh H LF 1 ff2 fp2 FR2') as S2.
    repeat match type of S1 with Forall _ (_ :: _) => apply Forall_cons_iff in S1 as [? S1] end.
    repeat match type of S2 with Forall _ (_ :: _) => apply Forall_cons_iff in S2 as [? S2] end.
    unfold XSq. repeat apply Forall_cons; try apply Forall_nil; assumption.
  Qed.

  Lemma wbc_laws : forall LBx LBr ff1 fp1 spa ff2 fp2, qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 ->
    fresh_frame H LF 1 ff1 fp1 -> fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    let P := fun W => Forall (aclient_write_ok H LBx) W /\ Forall stack0_ok W
                     /\ Forall (LbB_HKit.wmix LBr spz ([(ds, ds + DS_SIZE)] ++ XSq ff1 fp1 ff2 fp2)) W
                     /\ (forall a, ds <= a < ds + DS_SIZE -> ~ (ds + 136 <= a < ds + 144) -> ~ (ds + 256 <= a < ds + 260) -> outside W a)
                     /\ disjoint_from W (errno_addr tp) 4
                     /\ (forall A k, AIMG_TOP <= A -> A + k <= aceil -> (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) -> (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) ->
                           (ds + DS_SIZE <= A \/ A + k <= ds) -> disjoint_from W A k)
                     /\ (forall A k, AIMG_TOP <= A -> 0 <= k -> A + k <= aceil -> A mod 8 = 0 ->
                           (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) -> (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> disjoint_from W (sh A) (nsh k)) in
    P (WBq ff1 fp1 ff2 fp2) /\ P (WCq ff1 fp1 spa ff2 fp2).
  Proof.
    intros LBx LBr ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2.
    pose proof (nums2q ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU.
    pose proof (djs2q ff1 fp1 spa ff2 fp2 G1 G2) as (SIDE & XF1D & XP1D & SF1D & XF2D & XP2D & SF2D & XF12 & XP12 & SF12).
    destruct (fr_placeq LF ff1 fp1 FR1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AP & _ & _ & _ & _ & _ & _ & Z7 & A1).
    assert (TP : tp = Z_to_bv 64 ATP) by (destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _); exact TP).
    assert (SA : 0x7fff7000 <= sh aceil) by (clear - A1; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    assert (ERR : errno_addr tp + 4 <= 0x6e8000) by (rewrite TP, unsigned_lit by (clear; unfold ATP; lia); clear; unfold ATP; cbn; lia).
    set (e := errno_addr tp) in *. clearbody e.
    assert (ONE : forall lo1 hi1,
      (   (lo1 = spz - 16384 /\ hi1 = spz) \/ (lo1 = as_FSB H /\ hi1 = as_FSB H + AFS_FLAGS)
       \/ (lo1 = fp1 /\ hi1 = fp1 + 1) \/ (lo1 = ff1 /\ hi1 = ff1 + 128) \/ (lo1 = sh ff1 /\ hi1 = sh ff1 + 16)
       \/ (lo1 = fp2 /\ hi1 = fp2 + 1) \/ (lo1 = ff2 /\ hi1 = ff2 + 128) \/ (lo1 = sh ff2 /\ hi1 = sh ff2 + 16)
       \/ (lo1 = ds + 256 /\ hi1 = ds + 260) \/ (lo1 = ds + 136 /\ hi1 = ds + 144)) ->
      aclient_write_ok H LBx (lo1, hi1) /\ stack0_ok (lo1, hi1)
      /\ LbB_HKit.wmix LBr spz ([(ds, ds + DS_SIZE)] ++ XSq ff1 fp1 ff2 fp2) (lo1, hi1)
      /\ (forall a, ds <= a < ds + DS_SIZE -> ~ (ds + 136 <= a < ds + 144) -> ~ (ds + 256 <= a < ds + 260) -> ~ (lo1 <= a < hi1))
      /\ (e + 4 <= lo1 \/ hi1 <= e)
      /\ (forall A k, AIMG_TOP <= A -> A + k <= aceil -> (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) -> (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) ->
            (ds + DS_SIZE <= A \/ A + k <= ds) -> A + k <= lo1 \/ hi1 <= A)
      /\ (forall A k, AIMG_TOP <= A -> 0 <= k -> A + k <= aceil -> A mod 8 = 0 -> (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) ->
            (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> sh A + nsh k <= lo1 \/ hi1 <= sh A)).
    { intros lo1 hi1 CASE. unfold AFS_FLAGS, AFS_SIZE, DS_SIZE in CASE. unfold aclient_write_ok, stack0_ok, LbB_HKit.wmix, XSq, DS_SIZE, AFS_FLAGS, AFS_SIZE, AIMG_TOP, AHI_LO. cbn [fst snd]. rewrite fsz_1, fshn_1.
      assert (SHK : forall A k, 0x6e8000 <= A -> 0 <= k -> A + k <= aceil -> A mod 8 = 0 ->
                 0x800d5000 <= sh A /\ sh A + nsh k + 2040 <= sh spz /\ 0 <= nsh k /\ True
                 /\ (A + k + 16 <= as_FSB H -> sh A + nsh k + 1 <= sh (as_FSB H))
                 /\ (as_FSB H + 11571200 <= A - 16 -> sh (as_FSB H + 11571200) + 2 <= sh A) /\ True /\ True).
      { intros A k HA Hk HK H8. assert (SZ : aceil + 16384 <= spz) by (clear - NU; lia). clear - HA Hk HK H8 SZ. unfold sh, nsh, ASHADOW_BASE in *.
        repeat match goal with |- _ /\ _ => split end; try exact I; Z.div_mod_to_equations; lia. }
      assert (SHC : sh (as_FSB H + 11571200) <= sh aceil /\ sh aceil + 2 ^ 44 + 2048 <= spz /\ sh aceil <= sh spz)
        by (clear - NU Z7 A1; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
      destruct CASE as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]]].
      - split; [left; clear - NU; lia|]. split; [left; clear - NU A1; lia|]. split; [left; clear - NU; lia|].
        split; [intros a Ha _ _; clear - Ha NU; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X2 NU; lia|]. intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & _); clear - Y2 SHC NU; lia.
      - split; [do 4 right; left; clear; lia|]. split; [clear - SIDE SA NU; destruct SIDE; [right | left]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ _; clear - Ha NU; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X3 NU; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - Y1 Y2 Y7 SHC SIDE NU X5; lia.
      - split; [do 4 right; left; clear - NU; lia|]. split; [clear - SIDE SA NU; destruct SIDE; [right | left]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ _; clear - Ha NU XP1D; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X3 NU; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - Y1 Y2 Y7 SHC SIDE NU X5; lia.
      - split; [do 4 right; left; clear - NU; lia|]. split; [clear - SIDE SA NU; destruct SIDE; [right | left]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ _; clear - Ha NU XF1D; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X3 NU; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - Y1 Y2 Y7 SHC SIDE NU X5; lia.
      - split; [do 5 right; left; clear - NU; lia|]. split; [right; clear - NU SHC; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ _; clear - Ha NU SIDE; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X1 X2 X3 X5 NU SIDE SHC; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - X3 Y5 Y6 NU; lia.
      - split; [do 4 right; left; clear - NU; lia|]. split; [clear - SIDE SA NU; destruct SIDE; [right | left]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ _; clear - Ha NU XP2D; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X3 NU; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - Y1 Y2 Y7 SHC SIDE NU X5; lia.
      - split; [do 4 right; left; clear - NU; lia|]. split; [clear - SIDE SA NU; destruct SIDE; [right | left]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ _; clear - Ha NU XF2D; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X3 NU; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - Y1 Y2 Y7 SHC SIDE NU X5; lia.
      - split; [do 5 right; left; clear - NU; lia|]. split; [right; clear - NU SHC; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ _; clear - Ha NU SIDE; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X1 X2 X3 X5 NU SIDE SHC; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - X3 Y5 Y6 NU; lia.
      - split; [do 4 right; left; clear - NU; lia|]. split; [clear - SIDE SA NU; destruct SIDE; [right | left]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha _ X; clear - Ha X; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X4; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - Y1 Y2 Y7 SHC SIDE NU X5; lia.
      - split; [do 4 right; left; clear - NU; lia|]. split; [clear - SIDE SA NU; destruct SIDE; [right | left]; lia|].
        split; [right; left; intros a Ha; cbn [rin_ivs app fst snd]; clear - Ha; lia|].
        split; [intros a Ha X _; clear - Ha X; lia|]. split; [clear - ERR NU; lia|].
        split; [intros A k X1 X2 X3 X5 X4; clear - X4; lia|].
        intros A k X1 X0 X2 X8 X3 X5; destruct (SHK A k X1 X0 X2 X8) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8); clear - Y1 Y2 Y7 SHC SIDE NU X5; lia. }
    assert (GEN : forall W, Forall (fun iv => (   (fst iv = spz - 16384 /\ snd iv = spz) \/ (fst iv = as_FSB H /\ snd iv = as_FSB H + AFS_FLAGS)
       \/ (fst iv = fp1 /\ snd iv = fp1 + 1) \/ (fst iv = ff1 /\ snd iv = ff1 + 128) \/ (fst iv = sh ff1 /\ snd iv = sh ff1 + 16)
       \/ (fst iv = fp2 /\ snd iv = fp2 + 1) \/ (fst iv = ff2 /\ snd iv = ff2 + 128) \/ (fst iv = sh ff2 /\ snd iv = sh ff2 + 16)
       \/ (fst iv = ds + 256 /\ snd iv = ds + 260) \/ (fst iv = ds + 136 /\ snd iv = ds + 144))) W ->
       Forall (aclient_write_ok H LBx) W /\ Forall stack0_ok W
       /\ Forall (LbB_HKit.wmix LBr spz ([(ds, ds + DS_SIZE)] ++ XSq ff1 fp1 ff2 fp2)) W
       /\ (forall a, ds <= a < ds + DS_SIZE -> ~ (ds + 136 <= a < ds + 144) -> ~ (ds + 256 <= a < ds + 260) -> outside W a)
       /\ disjoint_from W e 4
       /\ (forall A k, AIMG_TOP <= A -> A + k <= aceil -> (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) ->
             (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> (ds + DS_SIZE <= A \/ A + k <= ds) -> disjoint_from W A k)
       /\ (forall A k, AIMG_TOP <= A -> 0 <= k -> A + k <= aceil -> A mod 8 = 0 ->
             (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) -> (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> disjoint_from W (sh A) (nsh k))).
    { intros W HW. induction W as [|[lo1 hi1] W IH].
      - repeat split; try apply Forall_nil; try (intros; exact I).
      - apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd] in H1. destruct (ONE lo1 hi1 H1) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
        destruct (IH HW) as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
        split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|].
        split; [intros a Ha Hb Hc; cbn [outside]; split; [exact (O4 a Ha Hb Hc) | exact (I4 a Ha Hb Hc)]|].
        split; [cbn [disjoint_from]; split; [exact O5 | exact I5]|].
        split; [intros A k X1 X2 X3 X5 X4; cbn [disjoint_from]; split; [exact (O6 A k X1 X2 X3 X5 X4) | exact (I6 A k X1 X2 X3 X5 X4)]|].
        intros A k X1 X0 X2 X8 X3 X5; cbn [disjoint_from]; split; [exact (O7 A k X1 X0 X2 X8 X3 X5) | exact (I7 A k X1 X0 X2 X8 X3 X5)]. }
    split; apply GEN; unfold LbB_Pq.WB, LbB_Pq.WC; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear; tauto.
  Qed.

  Ltac evWW := cbn [edenot]; unfold wenv, HLib.Eseed, reg_ev, LbB_PqK2.W2, LbB_PqK.W1;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app length N.of_nat Pos.of_succ_nat Pos.succ N.add Pos.add].

  Ltac rgq HRT r e E := assert (E := rtbl_In _ _ _ r e HRT ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)); cbv beta in E; revert E; evWW; intros E.

  Lemma fin_post : forall ff1 fp1 spa ff2 fp2 Wb mb R' m' sX msF' mo' LB' DB' ms' pp' hm' fillb,
    qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 -> fresh_frame H LF 1 ff1 fp1 -> fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    (Wb = WBq ff1 fp1 ff2 fp2 \/ Wb = WCq ff1 fp1 spa ff2 fp2) ->
    pq_fin H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n lo LF fl ff1 fp1 spa ff2 fp2 Wb mb R' m' ->
    as_VIS H sX msF' = MS R' F (ret_pc (PropExec.getr R' 1)) fc None m' (seg_rom asegs) ->
    as_AKREL H sX (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    ds_rep_w LB' mb ds err (len + n) DB' ms' pp' hm' fl fillb -> Permutation LB' (DB' ++ LBk) -> lb_own DB' mb ->
    as_RHEAP H sX LB' mb -> as_rauxv_ok H mb B -> (exists e : word, rw_cells asegs mb (errno_addr tp) [C4 e]) -> stack0 mb lo shi ->
    xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ XSq ff1 fp1 ff2 fp2) m mb ->
    as_AL H sX >= as_AL H s - ds_cost (len + n) -> ds_xfer LB DB LB' DB' ->
    ds_post H LINV_P5 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBk LF [(ds, ds + DS_SIZE)] (ds_cost (len + n)) lo B shi m mo
            (Some ds) (ds_op_Q ds_repA0 LB DB ds err (len + n)) (mkCfg msF' mo').
  Proof.
    intros ff1 fp1 spa ff2 fp2 Wb mb R' m' sX msF' mo' LB' DB' ms' pp' hm' fillb G1 G2 FR1 FR2 HWb FIN VIS' KR' MP' REP' PERM' OWN' RH' RAUX' [e ERR'] S0'
           XP' AL' XFER.
    destruct FIN as [RF' HRT' Q1' MI' RFS' FI' W0' MU' WM'].
    destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                     & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
    pose proof (nums2q ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU.
    destruct (wbc_laws LB' DB' ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as [LWB LWC].
    assert (LAWS : Forall (aclient_write_ok H LB') Wb /\ Forall stack0_ok Wb
                   /\ Forall (LbB_HKit.wmix DB' spz ([(ds, ds + DS_SIZE)] ++ XSq ff1 fp1 ff2 fp2)) Wb
                   /\ (forall a, ds <= a < ds + DS_SIZE -> ~ (ds + 136 <= a < ds + 144) -> ~ (ds + 256 <= a < ds + 260) -> outside Wb a)
                   /\ disjoint_from Wb (errno_addr tp) 4
                   /\ (forall A k, AIMG_TOP <= A -> A + k <= aceil -> (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) -> (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) ->
                         (ds + DS_SIZE <= A \/ A + k <= ds) -> disjoint_from Wb A k)
                   /\ (forall A k, AIMG_TOP <= A -> 0 <= k -> A + k <= aceil -> A mod 8 = 0 ->
                         (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) -> (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> disjoint_from Wb (sh A) (nsh k))).
    { destruct HWb as [-> | ->]; [exact LWB | exact LWC]. }
    clear LWB LWC. destruct LAWS as (L1 & L2 & L3 & L4 & L5 & L6 & L7).

    rgq HRT' (1%bv : reg) (EVar 34) G1r. rgq HRT' (2%bv : reg) (EVar 33) G2r. rgq HRT' (3%bv : reg) (EVar 49) G3r. rgq HRT' (4%bv : reg) (EVar 50) G4r.
    rgq HRT' (8%bv : reg) (EVar 37) G8r. rgq HRT' (9%bv : reg) (EVar 38) G9r. rgq HRT' (10%bv : reg) (EVar 32) G10r.
    rgq HRT' (18%bv : reg) (EVar 39) G18r. rgq HRT' (19%bv : reg) (EVar 40) G19r. rgq HRT' (20%bv : reg) (EVar 41) G20r.
    rgq HRT' (21%bv : reg) (EVar 42) G21r. rgq HRT' (22%bv : reg) (EVar 43) G22r. rgq HRT' (23%bv : reg) (EVar 44) G23r.
    rgq HRT' (24%bv : reg) (EVar 45) G24r. rgq HRT' (25%bv : reg) (EVar 46) G25r. rgq HRT' (26%bv : reg) (EVar 47) G26r.
    rgq HRT' (27%bv : reg) (EVar 48) G27r.
    rewrite (MS_full_eq R' F _ fc m' _ RF') in VIS'.
    rewrite G1r, G2r, G3r, G4r, G8r, G9r, G10r, G18r, G19r, G20r, G21r, G22r, G23r, G24r, G25r, G26r, G27r in VIS'.

    pose proof REP' as (DI' & BLK' & DSA' & DSW' & DSO' & SBA').
    pose proof Q1' as [AC' LV' ST' DSAm DSWm _ _ _ _ _].
    assert (BLKF : forall q A k, In (q, A, k) DB' ->
              AIMG_TOP <= A /\ 0 <= k /\ A + k <= aceil /\ A mod 8 = 0 /\ (A + k + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16)
              /\ (A + k <= 0x7fff7000 \/ 0x10007fff8000 <= A) /\ (ds + DS_SIZE <= A \/ A + k <= ds)).
    { intros q A k Hin.
      assert (HinL : In (q, A, k) LB') by (eapply Permutation_in; [apply Permutation_sym; exact PERM' | apply in_app_iff; left; exact Hin]).
      pose proof (ah_blocks H HH _ _ _ (q, A, k) RH' HinL) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
      assert (DJ : ds + DS_SIZE <= A \/ A + k <= ds).
      { destruct ms' as [|d asz]; cbn [ds_blk] in BLK'; [rewrite BLK' in Hin; destruct Hin|].
        destruct BLK' as (pid & EDB & _). rewrite EDB in Hin. destruct Hin as [Hin|[]]. injection Hin. intros <- <- _.
        pose proof (di_dj _ _ _ _ _ _ _ _ _ _ _ DI' d asz eq_refl). unfold DS_SIZE. clear - H0. lia. }
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - clear - R16. Z.div_mod_to_equations. lia.
      - clear - RAPP. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP, AAPP_HI in RAPP. lia. }
    assert (REPm : ds_rep_w LB' m' ds err (len + n) DB' ms' pp' hm' fl 32).
    { split; [| split; [exact BLK' | split; [exact DSAm | split; [exact DSWm | split; [exact DSO' |]]]]].
      - eapply (ds_inv_reios _ mb m'); [exact DI' | right; reflexivity | exact W0' | exact FI' | |].
        + apply LbB_DRep.mdef_of_wr_at_hi; [exact DSWm | exact (proj1 DSO')].
        + intros a Ha HF X1 X2. apply MU'. rewrite unsigned_lit by exact Ha.
          destruct HF as [HD | (q & k & Hqk & Hr)].
          * apply L4; [exact HD | exact X1 | exact X2].
          * rewrite (ds_blk_lbl _ _ _ BLK') in Hqk.
            assert (Hin : exists pid, In (pid, q, k) DB').
            { destruct ms' as [|d asz]; cbn [str_blocks] in Hqk; [destruct Hqk|]. destruct Hqk as [Hqk|[]]. injection Hqk. intros <- <-.
              cbn [ds_blk] in BLK'. destruct BLK' as (pid & EDB & _). exists pid. rewrite EDB. left. reflexivity. }
            destruct Hin as [pid Hin]. destruct (BLKF pid q k Hin) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
            pose proof (L6 q k B1 B3 B5 B6 B7) as D. clear - D Hr. induction Wb as [|[l h] W IH]; cbn [outside disjoint_from] in *; [exact I|].
            destruct D as [D1 D2]. split; [lia | exact (IH D2)].
      - destruct ms' as [|d asz]; cbn [sb_addr] in SBA' |- *; [exact I|]. destruct SBA' as [SAD SAO]. split; [| exact SAO].
        cbn [ds_blk] in BLK'. destruct BLK' as (pid & EDB & _).
        destruct (BLKF pid d asz ltac:(rewrite EDB; left; reflexivity)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
        eapply addressable_transport; [exact SAD | exact MU' | exact WM' | exact (L7 d asz B1 B2 B3 B4 B5 B6)]. }

    unfold ds_post. cbn [cfg_ms cfg_model].
    exists (PropExec.getr R' 5), (PropExec.getr R' 6), (PropExec.getr R' 7), (PropExec.getr R' 10), (PropExec.getr R' 11), (PropExec.getr R' 12),
           (PropExec.getr R' 13), (PropExec.getr R' 14), (PropExec.getr R' 15), (PropExec.getr R' 16), (PropExec.getr R' 17),
           (PropExec.getr R' 28), (PropExec.getr R' 29), (PropExec.getr R' 30), (PropExec.getr R' 31), m', e, sX, LB', (XSq ff1 fp1 ff2 fp2), F, fc.
    split; [rewrite VIS', G10r; reflexivity|]. split; [exact FZ|]. split; [intros d Hd; injection Hd; intros <-; exact G10r|].
    split; [exact KR'|]. split; [exact MP'|]. split; [exact MI'|]. split; [exact ST'|].
    split; [eapply rw_cells_transport; [exact ERR' | exact MU' | exact WM' | exact L5]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RAUX' | exact MU' | exact WM' | exact L1]|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH' | exact MU' | exact WM' | exact L1]|].
    split.
    { exists DB'. split; [exact XFER|]. split; [| split; [eapply lb_own_wmono; [exact OWN' | exact WM'] | exact DSWm]].
      apply ds_repA0_w. exists ms', pp', hm', fl, 32. exact REPm. }
    split; [exact (xsq_scratch ff1 fp1 ff2 fp2 FR1 FR2)|].
    split.
    { eapply xpres_trans; [exact XP'|].
      eapply (LbB_HKit.xpres_munch_mixed H HH sX LB' LBk DB' spz _ _ mb mb m' (xpres_refl _ _ _ _ _) RH'); [| | exact MU' | exact WM' | exact L3].
      - eapply Permutation_trans; [exact PERM' | apply Permutation_app_comm].
      - clear - NU. lia. }
    split; [exact RFS'|]. split; [exact AC'|].
    split; [eapply stack0_transport; [exact S0' | exact MU' | exact WM' | exact L2]|].
    split; [exact LV' | exact AL'].
  Qed.

  Lemma dsf_of_rep : forall LBx mx lenx DBx msx ppx hmx fillx, ds_rep_w LBx mx ds err lenx DBx msx ppx hmx fl fillx ->
    dsf ds fl mx /\ CRep.fld ASEGS mx (ds + 136) 8 0 /\ CRep.fld ASEGS mx (ds + 256) 4 fillx.
  Proof.
    intros LBx mx lenx DBx msx ppx hmx fillx (DI & BLK & DSA & DSW & DSO & SBA).
    pose proof DI as DI'. destruct DI'. pose proof di_ios as II. destruct II. pose proof di_sb as SB. destruct SB.
    assert (W8 : forall a, ds <= a -> a + 8 <= ds + DS_SIZE -> wr_at asegs mx a 8) by (intros a X Y; eapply wr_at_sub; [exact DSW | lia | lia | lia]).
    assert (W4 : forall a, ds <= a -> a + 4 <= ds + DS_SIZE -> wr_at asegs mx a 4) by (intros a X Y; eapply wr_at_sub; [exact DSW | lia | lia | lia]).
    unfold DS_SIZE in *.
    split; [constructor|split].
    - apply rw_cells_of_fld8; [exact di_vt | apply W8; lia].
    - apply rw_cells_of_fld8; [exact si_vt | apply W8; lia].
    - apply rw_cells_of_fld8; [exact ii_vt | apply W8; lia].
    - replace (ds + 120) with (ds + 112 + 8) by lia. apply rw_cells_of_fld4; [exact ii_flags | apply W4; lia].
    - replace (ds + 144) with (ds + 112 + 32) by lia. apply rw_cells_of_fld4; [exact ii_state | apply W4; lia].
    - replace (ds + 152) with (ds + 112 + 40) by lia. apply rw_cells_of_fld8; [exact ii_rdbuf | apply W8; lia].
    - replace (ds + 160) with (ds + 112 + 48) by lia. apply rw_cells_of_fld8; [exact ii_loc | apply W8; lia].
    - replace (ds + 248) with (ds + 112 + 136) by lia. apply rw_cells_of_fld8; [exact ii_tie | apply W8; lia].
    - replace (ds + 136) with (ds + 112 + 24) by lia. exact ii_width.
    - replace (ds + 256) with (ds + 112 + 144) by lia. exact ii_fill.
  Qed.

  Lemma pq_main : as_SR H (ds_post H LINV_P5 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBk LF [(ds, ds + DS_SIZE)] (ds_cost (len + n))
                                   lo B shi m mo (Some ds) (ds_op_Q ds_repA0 LB DB ds err (len + n))) (mkCfg msF mo).
  Proof.
    pose proof PRE as PRE'.
    destruct PRE' as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                      & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
    pose proof REPW as (DI0 & BLK0 & DSA0 & DSW0 & DSO0 & SBA0). pose proof (di_len0 _ _ _ _ _ _ _ _ _ _ _ DI0) as LEN0.
    assert (XFER0 : ds_xfer LB DB LB DB) by (exists LBk; split; exact PERM).
    assert (COST0 : as_AL H s >= as_AL H s - ds_cost (len + n)) by (unfold ds_cost; clear - LEN0 N0; lia).
    destruct (Z.eq_dec n 0) as [NZ | NP].
    -
      eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS).
      { eapply evt_cut; [apply (pq_s1 H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ds p n len err lo LF LB DB ms pp hm fl fill s CTX)|].
        intros ms1 (ff1 & fp1 & spa & R1 & m1 & -> & ST1).
        eapply evt_cut; [apply (PQARGS pq_s2 ff1 fp1 spa R1 m1 ST1)|]. intros ms2 (ff2 & fp2 & R2 & m2 & -> & ST2).
        pose proof ST2 as [G1 G2 FR1 FR2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
        eapply evt_cut; [apply (PQARGS pq_z NZ ff1 fp1 spa ff2 fp2 R2 m2 ST2)|]. intros ms3 (R3 & m3 & -> & FIN).
        pose proof FIN as [RF3 _ _ _ _ _ _ _ _].
        rewrite (MS_full_eq R3 F _ fc m3 _ RF3).
        apply pq_ret_ok.
        instantiate (1 := fun msx => exists ff1 fp1 spa ff2 fp2 R' m', msx = MS R' F (ret_pc (PropExec.getr R' 1)) fc None m' (seg_rom asegs)
           /\ qg1 H sp ds p n fl lo ff1 fp1 spa /\ qg2 H ds ff1 fp1 ff2 fp2 /\ fresh_frame H LF 1 ff1 fp1 /\ fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2
           /\ pq_fin H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n lo LF fl ff1 fp1 spa ff2 fp2 (WBq ff1 fp1 ff2 fp2) m R' m').
        cbv beta. exists ff1, fp1, spa, ff2, fp2, R3, m3.
        rewrite <- (MS_full_eq R3 F _ fc m3 _ RF3).
        split; [reflexivity|]. split; [exact G1|]. split; [exact G2|]. split; [exact FR1|]. split; [exact FR2 | exact FIN]. }
      intros msF1 mo1 KR1 MP1 (ff1 & fp1 & spa & ff2 & fp2 & R' & m' & E1 & G1 & G2 & FR1 & FR2 & FIN).
      apply (ah_done H HH).
      eapply (fin_post ff1 fp1 spa ff2 fp2 _ m R' m' s msF1 mo1 LB DB ms pp hm fill G1 G2 FR1 FR2 (or_introl eq_refl) FIN E1 KR1 MP1);
        [| exact PERM | exact OWN | exact RH | exact RAUX | exists errv; exact ERRN | exact S0 | apply xpres_refl | exact COST0 | exact XFER0].
      split; [| exact (conj BLK0 (conj DSA0 (conj DSW0 (conj DSO0 SBA0))))]. eapply LbB_DRep.ds_inv_mono; [exact DI0 | clear - N0; lia].
    -
      assert (NP' : 0 < n) by (clear - N0 NP; lia).
      eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS).
      { eapply evt_cut; [apply (pq_s1 H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ds p n len err lo LF LB DB ms pp hm fl fill s CTX)|].
        intros ms1 (ff1 & fp1 & spa & R1 & m1 & -> & ST1).
        eapply evt_cut; [apply (PQARGS pq_s2 ff1 fp1 spa R1 m1 ST1)|]. intros ms2 (ff2 & fp2 & R2 & m2 & -> & ST2).
        eapply evt_cut; [apply (PQARGS pq_x NP' ff1 fp1 spa ff2 fp2 R2 m2 ST2)|]. intros ms3 (R3 & m3 & -> & STX).
        apply evt_done.
        instantiate (1 := fun msx => exists ff1 fp1 spa ff2 fp2 R' m', msx = MS R' F (Z_to_bv 64 AXSP) fc None m' (seg_rom asegs)
           /\ pq_stx H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m ds p n lo LF fl ff1 fp1 spa ff2 fp2 R' m').
        cbv beta. exists ff1, fp1, spa, ff2, fp2, R3, m3. split; [reflexivity | exact STX]. }
      intros msF1 mo1 KR1 MP1 (ff1 & fp1 & spa & ff2 & fp2 & R1 & m1 & E1 & STX).
      destruct STX as [G1 G2 FR1 FR2 RF1 HRT1 HTS1 HTA1 HTF21 HTH21 HTF11 HTH11 Q1 X1 MI1 RFS1 FI1 W01 MUB1 WMB1].
      pose proof (nums2q ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU.
      pose proof (djs2q ff1 fp1 spa ff2 fp2 G1 G2) as (SIDE & XF1D & XP1D & SF1D & XF2D & XP2D & SF2D & XF12 & XP12 & SF12).
      destruct (wbc_laws LB DB ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as [(L1 & L2 & L3 & L4 & L5 & L6 & L7) _].
      pose proof Q1 as [AC1 LV1 ST1 DSA1 DSW1 DSV1 DF1 FW1 HW1 LW1]. pose proof X1 as [FW2 HW2 LW2].
      pose proof G1 as G1'. destruct G1' as [_ _ [SPA32 _] _ _ _ _ _ _].

      rewrite (MS_full_eq R1 F _ fc m1 _ RF1) in E1.
      rgq HRT1 (1%bv : reg) (ELit 1010580) K1. rgq HRT1 (2%bv : reg) (EAlu ALU_ADD (EVar 54) (ELit (-192))) K2. rgq HRT1 (4%bv : reg) (EVar 50) K4.
      rgq HRT1 (10%bv : reg) (EAlu ALU_ADD (EVar 32) (ELit 8)) K10. rgq HRT1 (11%bv : reg) (EVar 35) K11. rgq HRT1 (12%bv : reg) (EVar 36) K12.
      rewrite w_addm in K2 by (clear - NU; lia). replace (spa + -192) with (spa - 192) in K2 by (clear; lia).
      rewrite w_add in K10 by (clear - NU; lia).
      assert (U2 : bv_unsigned (PropExec.getr R1 2) = spa - 192) by (rewrite K2; apply unsigned_lit; clear - NU; lia).

      assert (PERM' : Permutation LB (LBk ++ DB)) by (eapply Permutation_trans; [exact PERM | apply Permutation_app_comm]).
      assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MUB1 | exact WMB1 | exact L1]).
      assert (RAUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact RAUX | exact MUB1 | exact WMB1 | exact L1]).
      assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]) by (eapply rw_cells_transport; [exact ERRN | exact MUB1 | exact WMB1 | exact L5]).
      assert (S01 : stack0 m1 lo shi) by (eapply stack0_transport; [exact S0 | exact MUB1 | exact WMB1 | exact L2]).
      assert (OWN1 : lb_own DB m1) by (eapply lb_own_wmono; [exact OWN | exact WMB1]).
      assert (XP1 : xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ XSq ff1 fp1 ff2 fp2) m m1).
      { eapply (LbB_HKit.xpres_munch_mixed H HH s LB LBk DB spz _ _ m m m1 (xpres_refl _ _ _ _ _) RH PERM'); [clear - NU; lia | exact MUB1 | exact WMB1 | exact L3]. }
      assert (REP1 : ds_rep_w LB m1 ds err len DB ms pp hm fl 32).
      { split; [| split; [exact BLK0 | split; [exact DSA1 | split; [exact DSW1 | split; [exact DSO0 |]]]]].
        - eapply (ds_inv_reios _ m m1); [exact DI0 | right; reflexivity | exact W01 | exact FI1 | |].
          + apply LbB_DRep.mdef_of_wr_at_hi; [exact DSW1 | exact (proj1 DSO0)].
          + intros a Ha HF X1' X2'. apply MUB1. rewrite unsigned_lit by exact Ha.
            destruct HF as [HD | (q & k & Hqk & Hr)]; [apply L4; [exact HD | exact X1' | exact X2']|].
            rewrite (ds_blk_lbl _ _ _ BLK0) in Hqk.
            destruct ms as [|d asz]; cbn [str_blocks] in Hqk; [destruct Hqk|]. destruct Hqk as [Hqk|[]]. injection Hqk. intros <- <-.
            cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
            pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RH INb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
            pose proof (di_dj _ _ _ _ _ _ _ _ _ _ _ DI0 d asz eq_refl) as DJ.
            assert (D : disjoint_from (WBq ff1 fp1 ff2 fp2) d asz).
            { apply L6; [exact RI | exact RC | exact RF | | unfold DS_SIZE; clear - DJ; lia].
              clear - RAPP. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP, AAPP_HI in RAPP. lia. }
            clear - D Hr. induction (WBq ff1 fp1 ff2 fp2) as [|[l h] W IH]; cbn [outside disjoint_from] in *; [exact I|].
            destruct D as [D1 D2]. split; [lia | exact (IH D2)].
        - destruct ms as [|d asz]; cbn [sb_addr] in SBA0 |- *; [exact I|]. destruct SBA0 as [SAD SAO]. split; [| exact SAO].
          cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
          pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RH INb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
          eapply addressable_transport; [exact SAD | exact MUB1 | exact WMB1 |].
          apply L7; [exact RI | exact Rn | exact RC | clear - R16; Z.div_mod_to_equations; lia | exact RF |].
          clear - RAPP. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP, AAPP_HI in RAPP. lia. }
      assert (SRC1 : srcx_keep H LBk ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) (spa - 192) [(ds, ds + DS_SIZE)] m1 p n).
      { apply (srcx_keep_LF H LBk LF); [| intros f Hf; right; right; exact Hf].
        apply (srcx_keep_sp H LBk LF spz); [| clear - NU; lia].
        eapply (srcx_keep_fwd H LBk LF spz _ (XSq ff1 fp1 ff2 fp2) m m1 p n SRCK (xsq_scratch ff1 fp1 ff2 fp2 FR1 FR2) XP1). }
      assert (DSIN2 : obj_inframe ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) ds DS_SIZE).
      { destruct DSIN as (f & Hf & A1 & A2). exists f. split; [right; right; exact Hf | split; [exact A1 | exact A2]]. }

      eapply (ah_seq H HH).
      { eapply ((LbB_PcXspS.xsp_okA H HHbp)
                  (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5)
                  (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10)
                  (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15)
                  (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20)
                  (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
                  (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30)
                  (PropExec.getr R1 31) F fc msF1 m1 mo1 s LB LBk DB ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) lo B shi errv ds err len p n ms pp hm fl 32).
        - unfold pc_pre. split; [exact E1|]. split; [exact RH1|]. split; [exact KR1|]. split; [exact RAUX1|].
          split; [rewrite U2; clear - SPB NU; lia|]. split; [exact BB|]. split; [rewrite U2; clear - SPA32; Z.div_mod_to_equations; lia|].
          split; [rewrite U2; exact (proj1 (stk_split asegs m1 lo (spa - 192) spz ST1 ltac:(clear - NU; lia)))|].
          split; [exact CEIL|]. split; [rewrite U2; clear - NU; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK; lia|].
          split; [rewrite K4; exact ERR1|]. split; [exact MI1|]. split; [rewrite K4; exact TP|].
          split; [rewrite K1, unsigned_lit by (clear; lia); reflexivity|].
          split; [exact LV1|]. split; [exact AC1|]. split; [exact RFS1|]. split; [exact S01|]. rewrite U2. clear - SPS NU. lia.
        - exact K10.
        - exact K11.
        - exact K12.
        - exact NP'.
        - exact REP1.
        - exact PERM.
        - exact OWN1.
        - split; [exact DSIN2 | split; [exact DSO0 | split; [exact (di_al _ _ _ _ _ _ _ _ _ _ _ DI0) | exact (di_pos _ _ _ _ _ _ _ _ _ _ _ DI0)]]].
        - rewrite U2. split; [clear - IAM; unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI in IAM; lia|]. split; [clear - IAM N0; unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI in IAM; lia|].
          split; [exact SRC1|]. split; [exact IAM|]. split; [| exact PDJ].
          clear - PSTK NU. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, ADS_STACK in *. lia.
        - exact LEN.
        - exact BS.
        - exact LBC.
        - exact BL.
        - exact COST.
        - exact TRok. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & e2 & s2x & LB2
                        & VIS2 & KR2 & MP2 & MI2 & STK2 & ERR2 & RAUX2 & RH2 & RFS2 & AC2 & S02 & LV2 & (DB' & ms' & pp' & hm' & PERM2 & REP2 & PP2 & OWN2 & XP2 & AL2)).
      cbn [cfg_ms cfg_model] in *. rewrite U2 in STK2, XP2. rewrite K4 in ERR2.
      assert (RPC : ret_pc (PropExec.getr R1 1) = Z_to_bv 64 APQ_XSRA) by (rewrite K1; unfold APQ_XSRA; apply ret_pc_even; [clear; lia | reflexivity]).
      rewrite RPC in VIS2.
      pose proof REP2 as (DI2 & BLK2 & DSA2 & DSW2 & DSO2 & SBA2). destruct (dsf_of_rep _ _ _ _ _ _ _ _ REP2) as (DF2 & W02 & FI2).

      assert (XP2k : xpres H LBk (spa - 192) [(ds, ds + DS_SIZE)] m1 m2).
      { pose proof (LbB_PcXspS.rep_facts) as RFx. clear RFx.
        destruct ms as [|d asz]; cbn [sbx] in XP2; [exact XP2|].
        cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
        eapply (xpres_drop_blk H HH s LB m1 LBk DB pid d asz (spa - 192) [(ds, ds + DS_SIZE)] m1 m2 RH1 PERM'); [rewrite EDB; left; reflexivity | clear - NU; lia |].
        exact XP2. }
      assert (XCL : forall A k, spa - 192 <= A \/ (as_FSB H <= A /\ A + k <= as_FSB H + AFS_SIZE) \/ (sh (as_FSB H) <= A /\ A + k <= sh (as_FSB H + AFS_SIZE)) ->
                   (A + k <= ds \/ ds + DS_SIZE <= A) -> xclient_range H LBk (spa - 192) [(ds, ds + DS_SIZE)] A k).
      { intros A k HA HD. split; [| apply Forall_cons; [cbn [fst snd]; clear - HD; lia | apply Forall_nil]].
        destruct HA as [HA|[HA|HA]]; [left; exact HA | do 4 right; left; exact HA | do 5 right; left; exact HA]. }
      assert (STK2' : stk asegs m2 lo spz).
      { eapply stk_join; [exact STK2|]. eapply (stk_hi_of_xpres H LBk _ m1 m2); [| exact XP2k |].
        - exact (proj2 (stk_split asegs m1 lo (spa - 192) spz ST1 ltac:(clear - NU; lia))).
        - intros a Ha K. cbn [rin_ivs fst snd] in K. clear - Ha K NU. unfold DS_SIZE in K. lia. }

      set (R4 := mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) u0 u1 u2 (PropExec.getr R1 8) (PropExec.getr R1 9)
                     (Z_to_bv 64 n) b1 b2 b3 b4 b5 b6 b7 (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21)
                     (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25) (PropExec.getr R1 26) (PropExec.getr R1 27)
                     u3 u4 u5 u6) in VIS2.
      assert (KP : forall r, In r KEPT -> PropExec.getr R4 r = PropExec.getr R1 r).
      { intros r Hr. subst R4. apply (getr_mkR_keptR R1); [reflexivity | exact Hr]. }
      assert (HRT4 : rtbl (LbB_PqK2.W2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) R4 RTQXR).
      { assert (HK : rtbl (LbB_PqK2.W2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) R4 (keptk RTQX)).
        { apply (rtbl_keep _ R1 R4 _ KEPT); [apply rtbl_keptk; exact HRT1 | apply rsub_keptk | exact KP]. }
        assert (HX : rtbl (LbB_PqK2.W2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) R4 [(10%bv, EVar 36)]).
        { unfold rtbl. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. subst R4. cbn [PropExec.getr mkR]. evWW. reflexivity. }
        apply (rtbl_sub _ _ _ _ (rtbl_app _ _ _ _ HK HX)). vm_compute. reflexivity. }
      assert (SHF : sh (as_FSB H) <= sh ff1 /\ sh (as_FSB H) <= sh ff2 /\ sh (as_FSB H + 0xb09000) = sh (as_FSB H + AFS_SIZE)) by (unfold AFS_SIZE; clear - NU; lia).
      destruct SHF as (SHF1 & SHF2 & SHE).
      assert (HTS2 := LbB_PcOvfS.ftbl_xpres H LBk (spa - 192) _ _ spz m1 m2 TS0 (-104) 0 HTS1 XP2k ltac:(vm_compute; reflexivity)
                        ltac:(apply XCL; [left | right]; clear - NU; unfold DS_SIZE; lia)).
      assert (HTA2 := LbB_PcOvfS.ftbl_xpres H LBk (spa - 192) _ _ spa m1 m2 AT3 (-192) 88 HTA1 XP2k ltac:(vm_compute; reflexivity)
                        ltac:(apply XCL; [left | right]; clear - NU; unfold DS_SIZE; lia)).
      assert (HTF22 := LbB_PcOvfS.ftbl_xpres H LBk (spa - 192) _ _ ff2 m1 m2 FT3 0 128 HTF21 XP2k ltac:(vm_compute; reflexivity)
                        ltac:(apply XCL; [right; left; unfold AFS_SIZE; clear - NU; lia | clear - XF2D; unfold DS_SIZE; lia])).
      assert (HTH22 := LbB_PcOvfS.ftbl_xpres H LBk (spa - 192) _ _ (ff2 / 8) m1 m2 HT3 SHBASE (SHBASE + 16) HTH21 XP2k ltac:(vm_compute; reflexivity)
                        ltac:(rewrite LbB_PqK2.shb2_eq; replace (SHBASE + 16 - SHBASE) with 16 by (clear; lia);
                              apply XCL; [right; right; rewrite <- SHE; clear - NU SHF2; lia | clear - NU SIDE; unfold DS_SIZE; lia])).
      assert (HTF12 := LbB_PcOvfS.ftbl_xpres H LBk (spa - 192) _ _ ff1 m1 m2 FT2 0 128 HTF11 XP2k ltac:(vm_compute; reflexivity)
                        ltac:(apply XCL; [right; left; unfold AFS_SIZE; clear - NU; lia | clear - XF1D; unfold DS_SIZE; lia])).
      assert (HTH12 := LbB_PcOvfS.ftbl_xpres H LBk (spa - 192) _ _ (ff1 / 8) m1 m2 HT2 SHBASE (SHBASE + 16) HTH11 XP2k ltac:(vm_compute; reflexivity)
                        ltac:(rewrite LbB_PqK.shb1_eq; replace (SHBASE + 16 - SHBASE) with 16 by (clear; lia);
                              apply XCL; [right; right; rewrite <- SHE; clear - NU SHF1; lia | clear - NU SIDE; unfold DS_SIZE; lia])).
      assert (HTD2 : ftbl (LbB_PqK2.W2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) ds m2 DT3).
      { apply ftbl_of_fld; [exact W02 | eapply wr_at_sub; [exact DSW2 | clear; lia | unfold DS_SIZE; clear; cbn; lia | clear; cbn; lia]
                           | clear - NU; lia | clear - NU; cbn; lia]. }
      destruct (LbB_DCtor.inframe_facts H HH _ m2 ds DS_SIZE RFS2 DSIN2 ltac:(unfold DS_SIZE; clear; lia) (proj1 DSO2)) as (_ & DSV2 & _ & _).
      assert (WRX : forall A k, wr_at asegs m1 A k -> (spa - 192 <= A \/ (as_FSB H <= A /\ A + k <= as_FSB H + AFS_SIZE) \/ (sh (as_FSB H) <= A /\ A + k <= sh (as_FSB H + AFS_SIZE))) ->
                   (A + k <= ds \/ ds + DS_SIZE <= A) -> wr_at asegs m2 A k).
      { intros A k W HA HD. eapply (xpres_wr_at H); [exact XP2k | exact W | apply XCL; [exact HA | exact HD]]. }
      assert (Q2 : qf1 sp ds fl lo ff1 fp1 m2).
      { constructor; [exact AC2 | exact LV2 | exact STK2' | exact DSA2 | exact DSW2 | exact DSV2 | exact DF2 | | |].
        - apply WRX; [exact FW1 | right; left; unfold AFS_SIZE; clear - NU; lia | clear - XF1D; unfold DS_SIZE; lia].
        - apply WRX; [exact HW1 | right; right; rewrite <- SHE; clear - NU SHF1; lia | clear - NU SIDE; unfold DS_SIZE; lia].
        - apply WRX; [exact LW1 | right; left; unfold AFS_SIZE; clear - NU; lia | clear - XP1D; unfold DS_SIZE; lia]. }
      assert (X2 : qx2 ff2 fp2 m2).
      { constructor.
        - apply WRX; [exact FW2 | right; left; unfold AFS_SIZE; clear - NU; lia | clear - XF2D; unfold DS_SIZE; lia].
        - apply WRX; [exact HW2 | right; right; rewrite <- SHE; clear - NU SHF2; lia | clear - NU SIDE; unfold DS_SIZE; lia].
        - apply WRX; [exact LW2 | right; left; unfold AFS_SIZE; clear - NU; lia | clear - XP2D; unfold DS_SIZE; lia]. }
      assert (STB : pq_stb H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n lo LF fl ff1 fp1 spa ff2 fp2 R4 m2).
      { constructor; [exact G1 | exact G2 | exact FR1 | exact FR2 | subst R4; apply rfull_mkR | exact HRT4 | exact HTS2 | exact HTA2 | exact HTD2
                     | exact HTF22 | exact HTH22 | exact HTF12 | exact HTH12 | exact Q2 | exact X2 | exact MI2 | exact RFS2 | exact FI2]. }

      eapply (ahh_evt_then H HH _ _ s2x msF2 _ mo2 KR2 VIS2).
      { eapply evt_cut; [apply (PQARGS pq_b ff1 fp1 spa ff2 fp2 R4 m2 STB)|]. intros ms3 (R5 & m5 & -> & FIN).
        pose proof FIN as [RF5 _ _ _ _ _ _ _ _].
        rewrite (MS_full_eq R5 F _ fc m5 _ RF5). apply pq_ret_ok.
        instantiate (1 := fun msx => exists R' m', msx = MS R' F (ret_pc (PropExec.getr R' 1)) fc None m' (seg_rom asegs)
           /\ pq_fin H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n lo LF fl ff1 fp1 spa ff2 fp2 (WCq ff1 fp1 spa ff2 fp2) m2 R' m').
        cbv beta. exists R5, m5. rewrite <- (MS_full_eq R5 F _ fc m5 _ RF5). split; [reflexivity | exact FIN]. }
      intros msF3 mo3 KR3 MP3 (R' & m' & E3 & FIN).
      apply (ah_done H HH).
      assert (XPm2 : xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ XSq ff1 fp1 ff2 fp2) m m2).
      { eapply xpres_trans; [exact XP1|]. eapply xpres_weaken; [exact XP2k | clear - NU; lia | intros b Hb; exact Hb |].
        intros a Ha. apply rin_ivs_app. left. exact Ha. }
      assert (ALf : as_AL H s2x >= as_AL H s - ds_cost (len + n)).
      { assert (BK : 8 * (blkof ms' - blkof ms) <= ds_cost (len + n)).
        { unfold ds_cost. destruct ms' as [|d' asz']; cbn [blkof].
          - destruct ms; cbn [blkof]; [clear - LEN0 N0; lia|].
            cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
            pose proof (ah_blocks H HH _ _ _ (pid, _, _) RH INb) as (_ & _ & Rn & _). cbn [blk_size snd] in Rn. clear - LEN0 N0 Rn. lia.
          - pose proof (di_asz _ _ _ _ _ _ _ _ _ _ _ DI2 d' asz' eq_refl) as AZ.
            destruct ms as [|d asz]; cbn [blkof]; [clear - LEN0 N0 AZ; lia|].
            cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb).
            pose proof (ah_blocks H HH _ _ _ (pid, _, _) RH INb) as (_ & _ & Rn & _). cbn [blk_size snd] in Rn. clear - LEN0 N0 Rn AZ. lia. }
        clear - AL2 BK. lia. }
      eapply (fin_post ff1 fp1 spa ff2 fp2 _ m2 R' m' s2x msF3 mo3 LB2 DB' ms' pp' hm' 32 G1 G2 FR1 FR2 (or_intror eq_refl) FIN E3 KR3);
        [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2] | exact MP3]
        | exact REP2 | exact PERM2 | exact OWN2 | exact RH2 | exact RAUX2 | exists e2; exact ERR2 | exact S02 | exact XPm2 | exact ALf |].
      exists LBk. split; [exact PERM | exact PERM2].
  Qed.

End PQS.

Theorem put_cseq_okA {HCEIL : HeapCeil} : forall H, asan_rt_hyps_bp H -> put_cseq_stmtA H LINV_P5 ds_repA0.
Proof.
  intros H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc msF m mo s LB LBk LF CH lo B shi errv ds err len p n DB PRE Ha0 Ha1 Ha2 REP PERM DSOB DSIN N0 P0 SRCK IAM PSTK PDJ LEN BS BL.
  apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
  exact (pq_main H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LBk LF CH lo B shi errv
           ds err len p n DB ms pp hm fl fill PRE Ha0 Ha1 Ha2 REPW PERM DSOB DSIN N0 P0 SRCK IAM PSTK PDJ LEN BS BL).
Qed.
