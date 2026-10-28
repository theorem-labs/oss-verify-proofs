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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmEntry LbB_PmEntry2 LbB_PmCall LbB_PiStmt LbB_PmGlue LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

#[local] Arguments pw_p {H} _.
#[local] Arguments pw_cons {H} _.
#[local] Arguments pw_user {H} _.
#[local] Arguments pw_diag {H} _.
#[local] Arguments pw_words {H} _.
#[local] Arguments pw_n {H} _.
#[local] Arguments pw_LB0 {H} _.
#[local] Arguments pw_s0 {H} _.
#[local] Arguments pw_lo {H} _.
#[local] Arguments pw_B {H} _.
#[local] Arguments pw_shi {H} _.

Lemma bv_unsigned_in_range_64 : forall (x : word), 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. Qed.

Section Init.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHi : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Definition pm_world (w0 : piw H) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (ff fp : Z)
      (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) : pmwA H :=
    PMWA H (pw_p w0) (pw_cons w0) (pw_user w0) (pw_diag w0) (pw_words w0) (pw_n w0)
         (bv_unsigned sp) (pmS1 (bv_unsigned sp)) ff fp (bv_unsigned ra)
         [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra] gp tp (pw_LB0 w0) LF CH m0 mo0 (pw_s0 w0) (pw_lo w0) (pw_B w0) (pw_shi w0).


  Definition pro_wins (spz ff fp : Z) : list (Z * Z) :=
    [(pmS1 spz - AFS_STACK, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 8); (sh ff, sh ff + fshn 8)].

  Lemma pmS1_facts : forall spz, 0 <= spz -> spz mod 16 = 0 -> spz - 864 <= pmS1 spz <= spz - 832 /\ pmS1 spz mod 32 = 0.
  Proof.
    intros spz H0 H16. unfold pmS1. pose proof (Z.mod_pos_bound (spz - 832) 32 ltac:(lia)). split; [lia|].
    pose proof (Z.div_mod (spz - 832) 32 ltac:(lia)). Z.div_mod_to_equations. lia.
  Qed.

  Lemma pro_obj : forall LF m spz ff fp O n,
    as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    fsobj H LF O n -> 0 <= O -> 0 <= n -> aapp O n ->
    disjoint_from (pro_wins spz ff fp) O n /\ disjoint_from (pro_wins spz ff fp) (sh O) (nsh n).
  Proof.
    intros LF m spz ff fp O n RF FF HS OB H0 Hn AP.
    pose proof (aapp_below_aceil O n AP) as Hc. pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (Htop : O + n <= AAPP_HI) by (unfold AAPP_HI; lia).
    pose proof (fs_scratch_of_fresh H LF 8 ff fp FF) as FS.
    assert (D : forall iv, In iv [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 8); (sh ff, sh ff + fshn 8)] ->
                (O + n <= fst iv \/ snd iv <= O) /\ (sh O + nsh n <= fst iv \/ snd iv <= sh O)).
    { intros iv Hin. pose proof (proj1 (Forall_forall _ _) FS iv Hin) as Hs.
      split; [exact (fsobj_scratch H HHi LF O n m iv RF OB H0 Hn Htop AP Hs) | exact (fsobj_scratch_sh H HHi LF O n m iv RF OB H0 Hn Htop Hs)]. }
    assert (SHc : sh O + nsh n <= aceil).
    { pose proof (sh_below_aceil (O + n + 8) ltac:(unfold AAPP_HI in *; lia)). unfold nsh, sh in *. Z.div_mod_to_equations. lia. }
    destruct (D _ (or_introl eq_refl)) as [D1 D1s]. destruct (D _ (or_intror (or_introl eq_refl))) as [D2 D2s].
    destruct (D _ (or_intror (or_intror (or_introl eq_refl)))) as [D3 D3s].
    destruct (D _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as [D4 D4s]. cbn [fst snd] in *.
    unfold pro_wins. cbn [disjoint_from]. repeat split; lia.
  Qed.

  Lemma sh_ff_top : forall ff, 0 <= ff -> ff mod 8 = 0 -> sh ff + fshn 8 = sh (ff + fsz 8).
  Proof. intros ff H0 H8. change (fsz 8) with (8 * 2048). rewrite sh_add8. reflexivity. Qed.

  Lemma pro_aclient : forall LF m spz ff fp LB, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    Forall (aclient_write_ok H LB) (pro_wins spz ff fp).
  Proof.
    intros LF m spz ff fp LB RF FF HS.
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    change (fsz 8) with 16384 in *.
    assert (Q1 : sh (as_FSB H) <= sh ff) by (apply sh_mono; unfold AFS_HDR in *; lia).
    assert (Q2 : sh (ff + 16384) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    pose proof (sh_ff_top ff ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) FF8) as Q3. change (fsz 8) with 16384 in Q3.
    unfold pro_wins. change (fsz 8) with 16384. repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
    - left. lia.
    - right; right; right; right; left. unfold AFS_FLAGS, AFS_SIZE. lia.
    - right; right; right; right; left. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS in *. lia.
    - right; right; right; right; left. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS in *. lia.
    - right; right; right; right; right; left. lia.
  Qed.

  Lemma pro_stack0 : forall LF m spz ff fp, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    Forall stack0_ok (pro_wins spz ff fp).
  Proof.
    intros LF m spz ff fp RF FF HS.
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). change (fsz 8) with 16384 in *.
    assert (SA : ALOWSH_LO <= sh aceil) by (unfold sh, ALOWSH_LO, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (Q2 : sh (ff + 16384) <= sh aceil) by (apply sh_mono; lia).
    pose proof (sh_ff_top ff ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) FF8) as Q3. change (fsz 8) with 16384 in Q3.
    unfold pro_wins. change (fsz 8) with 16384. unfold stack0_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - left. unfold AHI_LO. lia.
    - destruct FB3 as [(L1 & L2)|(L1 & L2)]; [right | left]; unfold ALOWSH_LO, AHI_LO, AFS_FLAGS, AFS_SIZE in *; lia.
    - destruct FB3 as [(L1 & L2)|(L1 & L2)]; [right | left]; unfold ALOWSH_LO, AHI_LO, AFS_HDR, AFS_SIZE, AFS_FLAGS in *; lia.
    - destruct FB3 as [(L1 & L2)|(L1 & L2)]; [right | left]; unfold ALOWSH_LO, AHI_LO, AFS_HDR, AFS_SIZE, AFS_FLAGS in *; lia.
    - right. lia.
  Qed.

  Lemma pro_img : forall LF m spz ff fp, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) (pro_wins spz ff fp).
  Proof.
    intros LF m spz ff fp RF FF HS.
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (sh AIMG_TOP <= sh ff) by (apply sh_mono; unfold AFS_HDR in *; lia).
    replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity.
    unfold pro_wins. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *; lia.
  Qed.

  Lemma disj_low : forall W a n, Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> a + n <= AIMG_TOP -> disjoint_from W a n.
  Proof.
    induction W as [|[lo hi] W IH]; intros a n FW Ha; cbn [disjoint_from]; [exact I|].
    pose proof (Forall_inv FW) as F1. cbn [fst] in F1. split; [lia | exact (IH a n (Forall_inv_tail FW) Ha)].
  Qed.

  Lemma disj_high : forall W a n, Forall (fun iv : Z * Z => snd iv <= a) W -> disjoint_from W a n.
  Proof.
    induction W as [|[lo hi] W IH]; intros a n FW; cbn [disjoint_from]; [exact I|].
    pose proof (Forall_inv FW) as F1. cbn [snd] in F1. split; [lia | exact (IH a n (Forall_inv_tail FW))].
  Qed.

  Lemma pro_below : forall LF m spz ff fp, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    pmS1 spz <= spz -> Forall (fun iv : Z * Z => snd iv <= spz) (pro_wins spz ff fp).
  Proof.
    intros LF m spz ff fp RF FF HS HS1. unfold AFS_STACK in *.
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). change (fsz 8) with 16384 in *.
    assert (Q2 : sh (ff + 16384) <= sh aceil) by (apply sh_mono; lia).
    assert (Q4 : sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    pose proof (sh_ff_top ff ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) FF8) as Q3. change (fsz 8) with 16384 in Q3.
    unfold pro_wins. change (fsz 8) with 16384.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *; lia.
  Qed.

  Lemma pro_xp : forall LF m spz ff fp p, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= spz) \/ (forall a, fst iv <= a < snd iv ->
               rin_ivs ((p, p + PARSER_SIZE) :: (ff, ff + fsz PM_FCLASS) :: (sh ff, sh ff + fshn PM_FCLASS)
                        :: [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1)]) a)) (pro_wins spz ff fp).
  Proof.
    intros LF m spz ff fp p RF FF HS. unfold pro_wins.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - left. lia.
    - right. intros a Ha. cbn [rin_ivs fst snd]. right; right; right; left. exact Ha.
    - right. intros a Ha. cbn [rin_ivs fst snd]. right; right; right; right; left. exact Ha.
    - right. intros a Ha. cbn [rin_ivs fst snd]. right; left. exact Ha.
    - right. intros a Ha. cbn [rin_ivs fst snd]. right; right; left. exact Ha.
  Qed.

  Definition e2_wins (S1 ff : Z) : list (Z * Z) := [(S1 + 680, S1 + 688); (ff, ff + 24); (sh ff, sh ff + 1448)].

  Lemma aconst_ok_of : forall lo hi, (0x6e8000 <= lo /\ sh AIMG_TOP <= lo) \/ (0x6e8000 <= lo /\ hi <= 0x7fff7000) ->
    aconst_ok (lo, hi).
  Proof.
    intros lo hi HLO.
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
      AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
      replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity;
      destruct HLO as [(L1 & L2)|(L1 & L2)]; lia.
  Qed.

  Lemma e2_props : forall LF m spz ff fp LB, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    pmS1 spz + 688 <= spz ->
    Forall (aclient_write_ok H LB) (e2_wins (pmS1 spz) ff) /\ Forall aconst_ok (e2_wins (pmS1 spz) ff)
    /\ Forall (afs_write_ok H ((8, ff, fp) :: LF)) (e2_wins (pmS1 spz) ff)
    /\ (forall x, outside (pro_wins spz ff fp) x -> outside (e2_wins (pmS1 spz) ff) x).
  Proof.
    intros LF m spz ff fp LB RF FF HS H64. unfold AFS_STACK in HS.
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). change (fsz 8) with 16384 in *.
    assert (Q1 : sh (as_FSB H) <= sh ff) by (apply sh_mono; unfold AFS_HDR in *; lia).
    assert (Q2 : sh (ff + 16384) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    pose proof (sh_ff_top ff ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) FF8) as Q3. change (fsz 8) with 16384 in Q3.
    change (fshn 8) with 2048 in Q3.
    assert (Q5 : sh AIMG_TOP <= sh ff) by (apply sh_mono; unfold AFS_HDR in *; lia).
    replace (sh AIMG_TOP) with 0x800d5000 in Q5 by reflexivity.
    split; [| split; [| split]].
    - unfold e2_wins. repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      + left. lia.
      + right; right; right; right; left. unfold AFS_HDR, AFS_SIZE in *. lia.
      + right; right; right; right; right; left. lia.
    - unfold e2_wins. repeat apply Forall_cons; try apply Forall_nil; apply aconst_ok_of.
      + left. replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. lia.
      + destruct FB3 as [(L1 & L2)|(L1 & L2)].
        * right. unfold AIMG_TOP, AFS_HDR, AFS_SIZE, ALOWSH_LO in *. lia.
        * left. replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. unfold AHI_LO, AFS_HDR in *. lia.
      + left. replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. unfold AIMG_TOP in *. lia.
    - unfold e2_wins. repeat apply Forall_cons; try apply Forall_nil; unfold afs_write_ok; cbn [fst snd].
      + left. unfold ATLS_PRIV_HI, ATP in *. split; [right | right]; lia.
      + right. exists (8, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (fsz 8) with 16384. lia.
      + left. split.
        * assert (R1 : 0 <= ff) by (unfold AIMG_TOP, AFS_HDR in FF1; lia).
          assert (R2 : ff + 16384 <= AAPP_HI) by (unfold AAPP_HI; lia).
          pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 16384 FB3 R1 R2 ltac:(lia)) as SH.
          unfold nsh in SH. change ((16384 + 7) / 8) with 2048 in SH. destruct SH as [SH|SH]; [left | right]; lia.
        * right. unfold ATLS_PRIV_HI, ATP in *. lia.
    - intros x Hx. unfold pro_wins, e2_wins in *. cbn [outside] in *. change (fsz 8) with 16384 in Hx. change (fshn 8) with 2048 in Hx.
      destruct Hx as (X1 & X2 & X3 & X4 & X5 & _). unfold AFS_STACK in *. repeat split; lia.
  Qed.

  Lemma pro_munch : forall spz ff fp m m1 m2, pmS1 spz + 688 <= spz -> spz - 864 <= pmS1 spz ->
    munch [(spz - 832, spz); (pmS1 spz - AFS_STACK, pmS1 spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1);
           (ff, ff + fsz 8); (sh ff, sh ff + fshn 8)] m m1 ->
    munch (e2_wins (pmS1 spz) ff) m1 m2 -> munch (pro_wins spz ff fp) m m2.
  Proof.
    intros spz ff fp m m1 m2 H1 H2 M1 M2 x Hx. transitivity (m1 x); [apply M2 | apply M1];
      unfold pro_wins, e2_wins in *; cbn [outside] in *; change (fsz 8) with 16384 in *; change (fshn 8) with 2048 in *;
      unfold AFS_STACK in *; destruct Hx as (X1 & X2 & X3 & X4 & X5 & _); repeat split; lia.
  Qed.

  Lemma disj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> disjoint_from W a' n'.
  Proof.
    induction W as [|[lo hi] W IH]; intros a n a' n' D H1 H2 H3; cbn [disjoint_from] in *; [exact I|].
    destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2 H3)].
  Qed.

  Lemma agree_of_disj : forall W m m' a n, munch W m m' -> disjoint_from W a n -> 0 <= a -> a + n <= 2 ^ 64 ->
    CRep.agree_on (zwin a (a + n)) m m'.
  Proof.
    intros W m m' a n MU D H0 H1 x Hx. unfold zwin in Hx. apply MU. rewrite unsigned_lit by lia.
    eapply disjoint_outside; [exact D | lia].
  Qed.

  Lemma fld_disj : forall W m m' a k v, munch W m m' -> disjoint_from W a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
    fld ASEGS m a k v -> fld ASEGS m' a k v.
  Proof.
    intros W m m' a k v MU D H0 H1 F. eapply fld_agree; [exact H0 | exact H1 | exact F |].
    eapply agree_of_disj; [exact MU | exact D | lia | lia].
  Qed.

  Lemma mdef_disj : forall W m m' a n, munch W m m' -> disjoint_from W a n -> 0 <= a -> a + n <= 2 ^ 64 -> mdef m a n -> mdef m' a n.
  Proof. intros W m m' a n MU D H0 H1 M. eapply mdef_agree; [exact M |]. eapply agree_of_disj; eassumption. Qed.

  Lemma lbl_blk : forall LB A n, In (A, n) (lbl LB) -> exists pid, In (pid, A, n) LB.
  Proof.
    intros LB A n Hin. unfold lbl in Hin. apply in_map_iff in Hin. destruct Hin as ([[pid A'] n'] & E & Hin). cbn in E.
    injection E as -> ->. exists pid. exact Hin.
  Qed.

  Lemma pro_blk : forall LF m spz ff fp s LB pid A n, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    as_RHEAP H s LB m -> In (pid, A, n) LB ->
    disjoint_from (pro_wins spz ff fp) A n /\ disjoint_from (pro_wins spz ff fp) (sh A) (nsh n).
  Proof.
    intros LF m spz ff fp s LB pid A n RF FF HS RH Hin.
    pose proof (ah_blocks H HHi _ _ _ _ RH Hin) as (B0 & _ & Bn & _ & _ & _ & BA). cbn [blk_addr blk_size fst snd] in *.
    apply (pro_obj LF m spz ff fp A n RF FF HS (fsobj_block H HHi s LB m LF pid A n RH Hin) ltac:(lia) Bn BA).
  Qed.

  Lemma e2_disj_stack : forall LF m spz ff fp a n, as_RFS H LF m -> fresh_frame H LF 8 ff fp ->
    pmS1 spz + 688 <= a -> aceil <= a -> disjoint_from (e2_wins (pmS1 spz) ff) a n.
  Proof.
    intros LF m spz ff fp a n RF FF H1 H2.
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). change (fsz 8) with 16384 in *.
    assert (Q2 : sh (ff + 16384) <= sh aceil) by (apply sh_mono; lia).
    assert (Q4 : sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    pose proof (sh_ff_top ff ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) FF8) as Q3. change (fsz 8) with 16384 in Q3. change (fshn 8) with 2048 in Q3.
    unfold e2_wins. cbn [disjoint_from]. repeat split; lia.
  Qed.

  Lemma e2_disj_frame : forall LF m spz ff fp a n, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    ff + 24 <= a -> a + n <= ff + 16384 -> 0 <= n -> disjoint_from (e2_wins (pmS1 spz) ff) a n.
  Proof.
    intros LF m spz ff fp a n RF FF HS H1 H2 H3. unfold AFS_STACK in HS.
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    change (fsz 8) with 16384 in *.
    assert (FAPP : aapp ff 16384) by (eapply aapp_sub; [exact FB3 | unfold AFS_HDR in *; lia | lia]).
    pose proof (aapp_disjoint_sh ff 16384 ff 16384 FAPP ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(unfold AAPP_HI; pose proof aceil_facts; lia) ltac:(lia)) as SH.
    unfold nsh in SH. change ((16384 + 7) / 8) with 2048 in SH.
    unfold e2_wins. cbn [disjoint_from]. repeat split; lia.
  Qed.

  Definition blk_apart (W : list (Z * Z)) (LB : list block) : Prop :=
    forall pid A n, In (pid, A, n) LB -> disjoint_from W A n /\ disjoint_from W (sh A) (nsh n).

  Lemma d_lbl_eq : forall W s LB m m' A n a, as_RHEAP H s LB m -> munch W m m' -> blk_apart W LB ->
    In (A, n) (lbl LB) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
  Proof.
    intros W s LB m m' A n a RH MU BA Hin Ha.
    destruct (lbl_blk LB A n Hin) as [pid Hb].
    pose proof (ah_blocks H HHi _ _ _ _ RH Hb) as (B0 & _ & Bn & _ & _ & _ & BAP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (aapp_below_aceil A n BAP) as Hc. pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct (BA pid A n Hb) as [D _].
    apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
  Qed.

  Lemma d_addr_lbl : forall W LB m m' A n, munch W m m' -> wmono asegs m m' -> blk_apart W LB ->
    In (A, n) (lbl LB) -> addressable m A n -> addressable m' A n.
  Proof.
    intros W LB m m' A n MU WM BA Hin AD. destruct (lbl_blk LB A n Hin) as [pid Hb]. destruct (BA pid A n Hb) as [_ Ds].
    eapply addressable_transport; [exact AD | exact MU | exact WM | exact Ds].
  Qed.

  Lemma d_SHAD_lbl : forall W LB m m' A n sbs, munch W m m' -> wmono asegs m m' -> blk_apart W LB ->
    In (A, n) (lbl LB) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs.
  Proof.
    intros W LB m m' A n sbs MU WM BA Hin Hl SH. destruct (lbl_blk LB A n Hin) as [pid Hb]. destruct (BA pid A n Hb) as [_ Ds].
    eapply SHAD_transport; [exact SH | exact MU | exact WM |]. eapply disj_sub; [exact Ds | lia | lia | lia].
  Qed.

  Lemma d_umapx : forall W s LB m m' NS (V : Type) (nval : mem -> Z -> V -> Prop)
      (nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v)
      obj bl bc ents,
    24 <= NS -> as_RHEAP H s LB m -> munch W m m' -> blk_apart W LB ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m obj bl bc ents -> disjoint_from W obj 40 -> 0 <= obj -> obj + 40 < 2 ^ 64 ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m' obj bl bc ents.
  Proof.
    intros W s LB m m' NS V nval nval_agree obj bl bc ents HNS RH MU BA U D H0 H1.
    eapply (umapx_agree ASEGS LY_A MI_A NS V nval nval_agree HNS); [exact U | | intros p0 n0 _ Hl; exact Hl].
    intros a Ha. pose proof U as U'. destruct U' as [_ _ _ _ _ _ Ublive _ _ _ _ _ _ _ Unode _].
    unfold umap_foot in Ha. destruct Ha as [Ha|[(Hbc & Ha)|(q & Hq & Ha)]].
    - apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
    - destruct Ublive as [[E _]|[_ Hl]]; [contradiction|].
      exact (d_lbl_eq W s LB m m' bl (8 * bc) a RH MU BA Hl Ha).
    - apply in_map_iff in Hq. destruct Hq as ([q' [k v]] & Eq & Hin). cbn in Eq. subst q'.
      destruct (Unode q k v Hin) as (Hl & _).
      exact (d_lbl_eq W s LB m m' q NS a RH MU BA Hl Ha).
  Qed.

  Lemma d_vec32 : forall W s LB m m' v b xs cap,
    as_RHEAP H s LB m -> munch W m m' -> blk_apart W LB ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m v b xs cap -> disjoint_from W v 24 -> 0 <= v -> v + 24 < 2 ^ 64 ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' v b xs cap.
  Proof.
    intros W s LB m m' v b xs cap RH MU BA V D H0 H1.
    eapply vec32_frame; [exact V|]. intros a Ha.
    pose proof V as (_ & _ & _ & Hlen & Hb & _). unfold vec32_fp in Ha. destruct Ha as [Ha|(Hb0 & Ha)].
    - apply MU. unfold zwin in Ha. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
    - destruct Hb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|]. unfold zwin in Ha.
      eapply (d_lbl_eq W s LB m m' b (4 * cap) a RH MU BA Hl). unfold Zlen in *. lia.
  Qed.

  Lemma d_vec_opnd : forall W LB m m' v b n cap,
    munch W m m' -> @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m v b n cap -> disjoint_from W v 24 -> 0 <= v -> v + 24 < 2 ^ 64 ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' v b n cap.
  Proof.
    intros W LB m m' v b n cap MU V D H0 H1.
    eapply vec_opnd_frame; [exact V|]. intros a Ha. unfold vec_opnd_fp, zwin in Ha.
    apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
  Qed.

  Lemma d_umap_sh : forall W LB m m' NS (V : Type) (nval : mem -> Z -> V -> Prop) obj bl bc ents,
    munch W m m' -> wmono asegs m m' -> blk_apart W LB ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m obj bl bc ents ->
    umap_sh m NS (bl, bc, ents) -> umap_sh m' NS (bl, bc, ents).
  Proof.
    intros W LB m m' NS V nval obj bl bc ents MU WM BA U [SB SN].
    destruct U as [_ _ _ _ _ _ Ublive _ _ _ _ _ _ _ Unode _]. cbn [t3a t3b t3c fst snd] in *. split.
    - intros Hbc. destruct Ublive as [[E _]|[_ Hl]]; [contradiction|].
      exact (d_addr_lbl W LB m m' bl (8 * bc) MU WM BA Hl (SB Hbc)).
    - intros q k v Hin. destruct (Unode q k v Hin) as (Hl & _).
      exact (d_addr_lbl W LB m m' q NS MU WM BA Hl (SN q k v Hin)).
  Qed.

  Lemma d_pmc_sh : forall W LB m m' p c, munch W m m' -> wmono asegs m m' -> blk_apart W LB ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (p + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m (p + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (p + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m (p + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (p + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (p + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) ->
    pmc_sh m c -> pmc_sh m' c.
  Proof.
    intros W LB m m' p c MU WM BA U1 U2 U3 V1 V2 V3 (S1 & S2 & S3 & S4 & S5 & S6).
    destruct (c_m1 c) as [[bl1 bc1] e1] eqn:E1. destruct (c_m2 c) as [[bl2 bc2] e2] eqn:E2. destruct (c_m3 c) as [[bl3 bc3] e3] eqn:E3.
    unfold pmc_sh. rewrite E1, E2, E3 in *. cbn [t3a t3b t3c fst snd] in *.
    split; [exact (d_umap_sh W LB m m' 24 Z (nval24 ASEGS) _ bl1 bc1 e1 MU WM BA U1 S1)|].
    split; [exact (d_umap_sh W LB m m' 32 (Z * Z * Z) (nval32 ASEGS) _ bl2 bc2 e2 MU WM BA U2 S2)|].
    split; [exact (d_umap_sh W LB m m' 24 Z (nval24 ASEGS) _ bl3 bc3 e3 MU WM BA U3 S3)|].
    split; [| split].
    - intros Hb. pose proof V1 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (d_SHAD_lbl W LB m m' _ _ _ MU WM BA Hl); [| exact (S4 Hb)].
      rewrite cc_gen_length by (unfold OPND_SZ; lia). lia.
    - intros Hb. pose proof V2 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (d_SHAD_lbl W LB m m' _ _ _ MU WM BA Hl); [| exact (S5 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
    - intros Hb. pose proof V3 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (d_SHAD_lbl W LB m m' _ _ _ MU WM BA Hl); [| exact (S6 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
  Qed.

  Lemma pmxa_tbl_perm : forall w s LB LBs m mo c ins tbl tbl2 ftbl TB spal,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> Permutation tbl tbl2 -> PMXAT H LINV w s LB LBs m mo c ins tbl2 ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl tbl2 ftbl TB spal X P.
    pose proof (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as Hs. unfold slots_ok in Hs.
    destruct X. constructor; try assumption.
    unfold slots_ok. apply Forall_forall. intros ke Hke.
    exact (proj1 (Forall_forall _ _) Hs ke (Permutation_in _ (Permutation_sym P) Hke)).
  Qed.

  Definition SH_P80 : expr := EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 80)) (ELit 3)) (ELit SHBASE).
  Definition RT_E2B : list (reg * expr) :=
    [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (11%bv, SH_P80); (16%bv, EVar WV_FF); (18%bv, EVar WV_FF);
     (20%bv, SH_FF); (23%bv, EVar WV_P); (25%bv, ELit SHBASE)].

  Lemma pm_init : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (w0 : piw H) (s : as_St H) (LB LBs : list block) (LF : list fframe) (CH : list (Z * Z)) (c : pmc) (Q : config -> Prop),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 APM_ENTRY) fc None m (seg_rom asegs) ->
      frm_zero fc -> a0 = Z_to_bv 64 (pw_p w0) -> tp = Z_to_bv 64 ATP ->
      piw_ok H w0 LF m -> PIX H LINV w0 s LB LBs m c -> c_widx c < pw_n w0 ->
      as_AKREL H s (mkCfg msF mo) ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= pw_B w0 -> bv_unsigned sp <= pw_shi w0 ->
      stk asegs m (pw_lo w0) (bv_unsigned sp) -> aceil <= pw_lo w0 -> pw_lo w0 <= bv_unsigned sp - APM_STACK ->
      bv_unsigned ra mod 2 = 0 ->
      as_RFS H LF m -> (length LF + PM_FRAMES <= AFS_MAXLIVE_BP)%nat ->
      as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) PM_PF (bv_unsigned ra) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pm_tr_ok H ->
      (forall (ff fp : Z) msF1 mo1 m1 R1,
         let w := pm_world w0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ff fp LF CH m mo in
         pmw_okA H w -> PI0A H LINV w s LB LBs m1 mo1 c msF1 R1 F fc -> as_SR H Q (mkCfg msF1 mo1)) ->
      as_SR H Q (mkCfg msF mo).
  Proof.
    intros until Q. intros VIS FZ Ha0 TP WOK X0 WN KR SP16 SPB SPS STK CE LO RA2 RFS LFB CHN HPF CHF HTR K.
    destruct WOK as [PKpobj PKpin PKpapp PKcobj PKcapp PKpcons PKcin PKmeas0 PKwords PKn PKB64 PKdiag].
    destruct X0 as [RH LBOWN [SO1 SO2] MEAS MI [errv ERR] RAUX AC S0 LI ALC PDEF PRcons PRuser PRhdr PRins PRhunk
                    PRwords PRn PRdiag PRwidx PRicount PRendian PRflags PRretry SCAL PRconsf PRconsd CWR WBUF
                    Xm1 Xm2 Xm3 Xv1 Xv2 Xv3 [PSH [PSp PSc]] Htr Hbsz Hic Hend Hw Hbud Hacc].
    set (spz := bv_unsigned sp) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. fold spz in Hspr.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m (pw_lo w0) (pw_shi w0) S0) as (SB1 & SB2 & SB3).
    eapply (pm_e1 H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
              (pw_p w0) (pw_lo w0) Q
              VIS KR Ha0 STK CE ltac:(unfold APM_STACK in LO; lia) SP16 ltac:(unfold AAPP_HI in *; lia) MI AC RH RFS
              ltac:(unfold PM_FRAMES in LFB; lia) TP).
    intros msF1 mo1 m1 ff fp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' KR1 MP1 VIS1 MU1 WM1 MI1 STK1 SAV1 RFS1 CL1 SH1 FLB1 AC1 RH1.
    pose proof (fresh_of_RFS H (HHi) _ _ _ _ _ RFS1) as FR.
    pose proof (fresh_frame_facts H _ _ _ _ FR) as (FK & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    change (fsz 8) with 16384 in *.
    assert (FAPP : aapp ff 16384) by (eapply aapp_sub; [exact FB3 | unfold AFS_HDR in *; lia | lia]).
    destruct PKpapp as (PAPP & P0 & P16).
    destruct PKcapp as (CAPP & C0 & C16).
    pose proof (aapp_below_aceil _ _ PAPP) as PTOP. pose proof (aapp_below_aceil _ _ CAPP) as CTOP.
    assert (P288 : pw_p w0 + 288 <= aceil) by (unfold PARSER_SIZE in PTOP; lia).
    eapply (pm_e2 H HHbp sp gp tp s2 s3 s4 s5 s6 s8 s10 s11 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc msF1 m1 mo1 s
              (pw_p w0) ff fp (pw_lo w0) Q
              VIS1 KR1 STK1 CE ltac:(unfold APM_STACK in LO; lia) SP16 ltac:(unfold AAPP_HI in *; lia) FF1
              ltac:(change (fsz 8) with 16384; lia) FF64 ltac:(change (fsz 8) with 16384; exact FAPP) SH1 CL1 P0 P288 MI1).
    intros msF2 mo2 m2 R2 KR2 MP2 VIS2 RF2 MU2 WM2 MI2 STK2 FSH2 HDR2 SLOT2 G2 G8 G9 G18 G23 G20 G10 G25 G16 G11 G3 G4
           G19 G21 G22 G24 G26 G27.
    fold spz in MU1, SAV1, CL1, MU2, SLOT2, G2, G9.
    set (w := pm_world w0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ff fp LF CH m mo).
    pose proof (pmS1_facts spz ltac:(lia) SP16) as (S1a & S1b).
    assert (OK : pmw_okA H w).
    { constructor; cbn [w pm_world wa_p wa_cons wa_user wa_diag wa_words wa_n wa_sp0 wa_s1 wa_ff wa_fp wa_ra wa_saved wa_gp wa_tp
                        wa_LB0 wa_LF0 wa_CH wa_m0 wa_mo0 wa_s0 wa_lo wa_B wa_shi]; fold spz.
      - exact FR.
      - exact PKpobj.
      - exact PKpin.
      - exact (conj PAPP (conj P0 P16)).
      - exact PKcobj.
      - exact (conj CAPP (conj C0 C16)).
      - exact PKpcons.
      - exact PKcin.
      - exact CHF.
      - exact (bv_unsigned_in_range_64 ra).
      - exact PKmeas0.
      - unfold APM_STACK in *. repeat split; try lia.
      - exact (conj S1a S1b).
      - exact TP.
      - exact RFS.
      - right. exact PKwords.
      - exact PKn.
      - reflexivity.
      - exact LFB.
      - exact PKB64.
      - exact PKdiag.
      - exact HTR.
      - exact HPF. }

    assert (HS : aceil <= pmS1 spz - AFS_STACK) by (unfold AFS_STACK, APM_STACK in *; lia).
    assert (H64 : pmS1 spz + 688 <= spz) by lia.
    unfold APM_STACK in LO.
    assert (Hff : 0 <= ff /\ ff + 16384 < 2 ^ 47) by (unfold AIMG_TOP, AFS_HDR in FF1; lia).
    pose proof (pro_munch spz ff fp m m1 m2 H64 ltac:(lia) MU1 MU2) as MU.
    pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM.
    pose proof (e2_props LF m spz ff fp LB RFS FR HS H64) as (E2A & E2C & E2F & E2O).
    pose proof (pro_aclient LF m spz ff fp LB RFS FR HS) as PA.
    pose proof (pro_stack0 LF m spz ff fp RFS FR HS) as PS0.
    pose proof (pro_img LF m spz ff fp RFS FR HS) as PI.
    pose proof (pro_below LF m spz ff fp RFS FR HS ltac:(lia)) as PB.
    destruct (pro_obj LF m spz ff fp (pw_p w0) PARSER_SIZE RFS FR HS PKpobj ltac:(lia) ltac:(unfold PARSER_SIZE; lia) PAPP) as [DP DPs].
    destruct (pro_obj LF m spz ff fp (pw_cons w0) 48 RFS FR HS PKcobj ltac:(lia) ltac:(lia) CAPP) as [DC DCs].
    assert (BA : blk_apart (pro_wins spz ff fp) LB).
    { intros pid A n Hin. exact (pro_blk LF m spz ff fp s LB pid A n RFS FR HS RH Hin). }
    assert (PF : forall k w1 v, 0 <= k -> k + Z.of_nat w1 <= PARSER_SIZE -> fld ASEGS m (pw_p w0 + k) w1 v -> fld ASEGS m2 (pw_p w0 + k) w1 v).
    { intros k w1 v Hk Hkw F0. eapply fld_disj; [exact MU | eapply disj_sub; [exact DP | lia | lia | lia] | lia | unfold PARSER_SIZE in *; lia | exact F0]. }

    assert (SAV2 : rw_cells asegs m2 (spz - 104) (map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra])).
    { eapply rw_cells_transport; [exact SAV1 | exact MU2 | exact WM2 |].
      apply (e2_disj_stack LF m spz ff fp _ _ RFS FR); lia. }
    destruct CL1 as (j1 & j2 & CL1).
    pose proof CL1 as CLw. destruct CLw as [_ FWR1].
    apply (rw_cells_app asegs m1 ff [CB 24 j1; C8 (Z_to_bv 64 (pmS1 spz)); CB 16344 j2] [C8 (Z_to_bv 64 fp)]) in CL1. destruct CL1 as [_ CLf].
    assert (CS3 : Z.of_nat (cells_size [CB 24 j1; C8 (Z_to_bv 64 (pmS1 spz)); CB 16344 j2]) = 16376) by reflexivity.
    rewrite CS3 in CLf.
    assert (FFL2 : rw_cells asegs m2 (ff + 16376) [C8 (Z_to_bv 64 fp)]).
    { eapply rw_cells_transport; [exact CLf | exact MU2 | exact WM2 |].
      apply (e2_disj_frame LF m spz ff fp _ _ RFS FR HS); cbn; lia. }
    assert (CS4 : Z.of_nat (cells_size [CB 24 j1; C8 (Z_to_bv 64 (pmS1 spz)); CB 16344 j2; C8 (Z_to_bv 64 fp)]) = 16384) by reflexivity.
    rewrite CS4 in FWR1.
    assert (FWR2 : wr_at asegs m2 ff 16384).
    { destruct FWR1 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. exact (WM2 _ (W3 i Hi)). }
    assert (CHN2 : as_chain H m2 spz ((spz, bv_unsigned ra) :: CH)).
    { apply (ah_chain_cons H HHi m2 (bv_unsigned s0) CH spz (bv_unsigned ra)).
      - eapply (chain_via_munch H HHi _ m m2 _ CH CHN MU). intros fp' ra' Hin. apply disj_high.
        eapply Forall_impl; [| exact PB]. intros iv Hiv. cbn beta in Hiv. pose proof (CHF fp' ra' Hin). lia.
      - exact (bv_unsigned_in_range_64 s0).
      - exact (bv_unsigned_in_range_64 ra).
      - exact SP16.
      - lia.
      - lia.
      - rewrite !Z_to_bv_bv_unsigned.
        assert (EM : map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra]
                     = map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1] ++ [C8 s0; C8 ra]) by reflexivity.
        pose proof SAV2 as SV. rewrite EM in SV. apply rw_cells_app in SV. destruct SV as [_ SV].
        rewrite cells_size_mapC8 in SV. cbn [length] in SV. replace (spz - 104 + Z.of_nat (8 * 11)) with (spz - 16) in SV by lia. exact SV. }

    assert (XA : PMXA H LINV w s LB LBs m2 mo2 c [] [(680, EVar WV_FF)] []).
    { constructor; cbn [w pm_world wa_p wa_cons wa_user wa_diag wa_words wa_n wa_sp0 wa_s1 wa_ff wa_fp wa_ra wa_saved wa_gp wa_tp
                        wa_LB0 wa_LF0 wa_CH wa_m0 wa_mo0 wa_s0 wa_lo wa_B wa_shi]; fold spz.
      - exact (ah_RHEAP_frame H HHi s LB m1 m2 _ RH1 MU2 WM2 E2A).
      - exact (lb_own_wmono _ _ _ LBOWN WM).
      - split; [apply lb_own_nil | cbn [length]; lia].
      - split; [rewrite app_nil_r; exact SO1 | exact SO2].
      - exact MEAS.
      - exact (ah_mpres_trans H HHi _ _ _ MP1 MP2).
      - exact MI2.
      - exact STK2.
      - exists errv. rewrite TP. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. apply disj_low; [exact PI |].
        rewrite unsigned_lit by (unfold ATP; lia). cbn [cells_size csize Nat.add]. unfold ATP, AIMG_TOP. lia.
      - exact (ah_rauxv_frame H HHi LB m m2 (pw_B w0) _ RAUX MU WM PA).
      - exact (ACONST_frame _ m1 m2 AC1 MU2 WM2 E2C).
      - exact (stack0_transport _ m m2 (pw_lo w0) (pw_shi w0) S0 MU WM PS0).
      - exact (LINV_frame m m2 _ LI MU WM PI).
      - exact (ah_RFS_frame H HHi _ m1 m2 _ RFS1 MU2 WM2 E2F).
      - exists [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1)]. split.
        + pose proof (fs_scratch_of_fresh H LF 8 ff fp FR) as FS.
          apply Forall_cons; [exact (Forall_inv FS) | apply Forall_cons; [exact (Forall_inv (Forall_inv_tail FS)) | apply Forall_nil]].
        + eapply (xpres_weaken H LB (pw_LB0 w0) spz spz
                    ((pw_p w0, pw_p w0 + PARSER_SIZE) :: (ff, ff + fsz PM_FCLASS) :: (sh ff, sh ff + fshn PM_FCLASS)
                     :: [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1)]));
            [| lia | | intros a Ha; right; exact Ha].
          * eapply (xpres_of_munch H s LB); [exact HHi | exact RH | exact MU | exact WM | exact (pro_xp LF m spz ff fp (pw_p w0) RFS FR HS)].
          * intros b Hb. apply (Permutation_in _ (Permutation_sym SO1)). apply in_app_iff. left. exact Hb.
      - destruct ALC as (AL1 & AL2 & AL3). split; [lia|]. split; [exact AL2|]. split; [exact AL3 | unfold PM_RESERVE; lia].
      - exact SAV2.
      - exact HDR2.
      - replace (ff + fsz PM_FCLASS - 8) with (ff + 16376) by (change (fsz PM_FCLASS) with 16384; lia). exact FFL2.
      - exact FWR2.
      - exact CHN2.
      - exact FSH2.
      - apply Forall_cons; [| apply Forall_nil]. exact SLOT2.
      - apply Forall_nil.
      - eapply mdef_disj; [exact MU | exact DP | lia | unfold PARSER_SIZE in *; lia | exact PDEF].
      - apply (PF 8 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact PRcons].
      - apply (PF 16 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact PRuser].
      - apply (PF 24 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact PRhdr].
      - apply (PF 32 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact PRins].
      - apply (PF 40 1%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact PRhunk].
      - apply (PF O_WORDS 8%nat); [unfold O_WORDS; lia | unfold O_WORDS, PARSER_SIZE; cbn; lia | exact PRwords].
      - apply (PF O_N 8%nat); [unfold O_N; lia | unfold O_N, PARSER_SIZE; cbn; lia | exact PRn].
      - apply (PF O_DIAG 8%nat); [unfold O_DIAG; lia | unfold O_DIAG, PARSER_SIZE; cbn; lia | exact PRdiag].
      - apply (PF O_WIDX 8%nat); [unfold O_WIDX; lia | unfold O_WIDX, PARSER_SIZE; cbn; lia | exact PRwidx].
      - apply (PF O_ICOUNT 8%nat); [unfold O_ICOUNT; lia | unfold O_ICOUNT, PARSER_SIZE; cbn; lia | exact PRicount].
      - apply (PF O_ENDIAN 4%nat); [unfold O_ENDIAN; lia | unfold O_ENDIAN, PARSER_SIZE; cbn; lia | exact PRendian].
      - apply (PF O_FLAGS 1%nat); [unfold O_FLAGS; lia | unfold O_FLAGS, PARSER_SIZE; cbn; lia | exact PRflags].
      - rewrite <- Z.add_assoc. apply (PF (O_FLAGS + 1) 1%nat); [unfold O_FLAGS; lia | unfold O_FLAGS, PARSER_SIZE; cbn; lia |].
        rewrite Z.add_assoc. exact PRretry.
      - exact SCAL.
      - eapply fld_disj; [exact MU | eapply disj_sub; [exact DC | lia | cbn; lia | lia] | lia | cbn; lia | exact PRconsf].
      - eapply mdef_disj; [exact MU | eapply disj_sub; [exact DC | lia | lia | lia] | lia | lia | exact PRconsd].
      - exact (wr_at_wmono _ _ _ _ CWR WM).
      - intros Hwz. destruct PKwords as (pw & k & Hin & Hk & W0 & W16 & Whi & Wdef & Wsh).
        assert (HinLB : In (pw, pw_words w0, k) LB) by (apply (Permutation_in _ (Permutation_sym SO1)); apply in_app_iff; left; exact Hin).
        destruct (pro_blk LF m spz ff fp s LB pw (pw_words w0) k RFS FR HS RH HinLB) as [DW _].
        eapply mdef_disj; [exact MU | eapply disj_sub; [exact DW | lia | lia | lia] | lia | lia | exact Wdef].
      - eapply (d_umapx _ s LB m m2 24 Z (nval24 ASEGS) (nval24_agree ASEGS)); [lia | exact RH | exact MU | exact BA | exact Xm1 | | unfold O_M1; lia | ].
        + eapply disj_sub; [exact DP | unfold O_M1; lia | unfold O_M1, PARSER_SIZE; lia | lia].
        + unfold O_M1, PARSER_SIZE in *; lia.
      - eapply (d_umapx _ s LB m m2 32 (Z * Z * Z) (nval32 ASEGS) (nval32_agree ASEGS)); [lia | exact RH | exact MU | exact BA | exact Xm2 | | unfold O_M2; lia | ].
        + eapply disj_sub; [exact DP | unfold O_M2; lia | unfold O_M2, PARSER_SIZE; lia | lia].
        + unfold O_M2, PARSER_SIZE in *; lia.
      - eapply (d_umapx _ s LB m m2 24 Z (nval24 ASEGS) (nval24_agree ASEGS)); [lia | exact RH | exact MU | exact BA | exact Xm3 | | unfold O_M3; lia | ].
        + eapply disj_sub; [exact DP | unfold O_M3; lia | unfold O_M3, PARSER_SIZE; lia | lia].
        + unfold O_M3, PARSER_SIZE in *; lia.
      - eapply (d_vec_opnd _ LB m m2); [exact MU | exact Xv1 | | unfold O_V1; lia | ].
        + eapply disj_sub; [exact DP | unfold O_V1; lia | unfold O_V1, PARSER_SIZE; lia | lia].
        + unfold O_V1, PARSER_SIZE in *; lia.
      - eapply (d_vec32 _ s LB m m2); [exact RH | exact MU | exact BA | exact Xv2 | | unfold O_V2; lia | ].
        + eapply disj_sub; [exact DP | unfold O_V2; lia | unfold O_V2, PARSER_SIZE; lia | lia].
        + unfold O_V2, PARSER_SIZE in *; lia.
      - eapply (d_vec32 _ s LB m m2); [exact RH | exact MU | exact BA | exact Xv3 | | unfold O_V3; lia | ].
        + eapply disj_sub; [exact DP | unfold O_V3; lia | unfold O_V3, PARSER_SIZE; lia | lia].
        + unfold O_V3, PARSER_SIZE in *; lia.
      - split; [| split].
        + exact (d_pmc_sh _ LB m m2 (pw_p w0) c MU WM BA Xm1 Xm2 Xm3 Xv1 Xv2 Xv3 PSH).
        + exact (addressable_transport _ m m2 (pw_p w0) PARSER_SIZE PSp MU WM DPs).
        + exact (addressable_transport _ m m2 (pw_cons w0) 48 PSc MU WM DCs). }

    assert (RT : regs_tbl w R2 RT_E2B).
    { unfold regs_tblX, RT_E2B. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - rewrite G2. reflexivity.
      - rewrite G8. transitivity (Z_to_bv 64 spz); [subst spz; symmetry; apply Z_to_bv_bv_unsigned | reflexivity].
      - rewrite G9. reflexivity.
      - rewrite G11. symmetry. apply sh_expr_val; [| reflexivity | lia].
        transitivity (alu64 ALU_ADD (Z_to_bv 64 (pw_p w0)) (Z_to_bv 64 80)); [reflexivity | apply w_add; lia].
      - rewrite G16. reflexivity.
      - rewrite G18. reflexivity.
      - rewrite G20. symmetry. apply sh_expr_val; [reflexivity | reflexivity | lia].
      - rewrite G23. reflexivity.
      - rewrite G25. reflexivity. }
    pm_go HHi LINV_frame OK XA KR2 VIS2 RF2 RT [Z_to_bv 64 (c_icount c)]
          (@nil kentry) 100%nat [PI0_PC] (@nil bool) 41%N
          (@nil nat) [576] (@nil Z) [(680, EVar WV_FF); (576, EVar WV_FF)] (@nil (Z * expr)) (RT_PI0 ++ [(10%bv, EVar 41)]).
    { pose proof (pmw_bounds H w OK) as BND.
      split_scs.
      eapply sc_rd_fld8; [exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA) | | reflexivity].
      rewrite (adenot_of_estart _ _ (wa_p w + O_ICOUNT)); [reflexivity | | unfold O_ICOUNT, PARSER_SIZE in *; lia].
      rewrite (estart_p H w _ _ OK (env_world_seed H w R2 [Z_to_bv 64 (c_icount c)])); reflexivity. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    assert (G3_3 : PropExec.getr R3 3%bv = gp) by (rewrite (HR3 3%bv); exact G3).
    assert (G4_3 : PropExec.getr R3 4%bv = tp) by (rewrite (HR3 4%bv); exact G4).
    apply Forall_app in HTx3. destruct HTx3 as [HTx3 HTa0].
    pose proof (Forall_inv HTa0) as A0_3. cbn [fst snd] in A0_3.
    rewrite (ev_xseed H w bvmap_empty [Z_to_bv 64 (c_icount c)] 41 (Z_to_bv 64 (c_icount c)) eq_refl eq_refl) in A0_3.
    pose proof (regs_tbl_restrict w [] _ R3 RT_PI0 HTx3 ltac:(vm_compute; reflexivity)) as HT3.
    pose proof (pmxa_tbl_perm _ _ _ _ _ _ _ _ _ TBL_PI0 _ _ _ X3 (perm_swap _ _ _)) as X4.
    lazymatch type of X4 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in X4 end.
    refine (K ff fp msF3 mo3 M3 R3 OK _).
    constructor; [exact X4 | exact KR3 | exact VIS3 | exact RF3 | exact FZ | exact HT3 | exact G3_3 | exact G4_3
                 | exact Htr | exact Hbsz | exact Hic | exact Hend | exact Hw | exact Hbud | exact Hacc | exact WN | exact A0_3].
  Qed.
End Init.
