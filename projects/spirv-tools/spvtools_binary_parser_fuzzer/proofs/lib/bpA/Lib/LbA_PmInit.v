(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmEntry LbA_PmEntry2 LbA_PmCall.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pmc_of (st : stateC) : pmc :=
  {| c_widx := st_widx st; c_icount := st_icount st; c_endian := st_endian st; c_reqconv := st_flags st;
     c_m1 := st_m1 st; c_m2 := st_m2 st; c_m3 := st_m3 st;
     c_v1 := (t3a (st_v1 st), 0, 25); c_v2 := (t3a (st_v2 st), [], 25); c_v3 := (t3a (st_v3 st), [], 25);
     c_tr := [] |}.

Lemma fresh_blocks : forall st words n, fresh_state st words n ->
  state_blocks st = [(t3a (st_v1 st), 500); (t3a (st_v2 st), 100); (t3a (st_v3 st), 100)]
  /\ c_blocks (pmc_of st) = [(t3a (st_v1 st), 500); (t3a (st_v2 st), 100); (t3a (st_v3 st), 100)].
Proof.
  intros [w0 n0 d0 wi ic en fl m1 m2 m3 [[b1 e1] c1] [[b2 e2] c2] [[b3 e3] c3]] words n
         (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
  cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 t3a t3b t3c fst snd] in *. subst m1 m2 m3 c1 c2 c3.
  unfold state_blocks, c_blocks, vec_blocks, vec_opnd_blocks, pmc_of, umap_blocks.
  cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 t3a t3b t3c fst snd Z.eqb map app].
  destruct (Z.eqb_spec b1 0); [contradiction|]. destruct (Z.eqb_spec b2 0); [contradiction|]. destruct (Z.eqb_spec b3 0); [contradiction|].
  unfold OPND_SZ. cbn [app]. split; repeat f_equal; lia.
Qed.

Lemma fold_perm : forall (f : Z * Z -> Z) l l', Permutation l l' ->
  fold_right (fun x acc => f x + acc) 0 l = fold_right (fun x acc => f x + acc) 0 l'.
Proof. intros f l l' P. induction P; cbn [fold_right]; lia. Qed.

Lemma lb_small_lbl : forall LB, lb_small LB = fold_right (fun x acc => nsmall (snd x) + acc) 0 (lbl LB).
Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbl in *. cbn [map fold_right]. rewrite lb_small_cons, IH. reflexivity. Qed.
Lemma nlarge_lbl : forall LB, nlarge LB = fold_right (fun x acc => nlg (snd x) + acc) 0 (lbl LB).
Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbl in *. cbn [map fold_right]. rewrite nlarge_cons, IH. reflexivity. Qed.
Lemma length_lbl : forall LB, length (lbl LB) = length LB.
Proof. intros LB. unfold lbl. apply length_map. Qed.

Lemma fresh_meas : forall (LBs : list block) st words n, fresh_state st words n -> Permutation (lbl LBs) (state_blocks st) -> 0 <= n ->
  pm_meas_ok n LBs.
Proof.
  intros LBs st words n FR P Hn. destruct (fresh_blocks st words n FR) as [E _]. rewrite E in P.
  unfold pm_meas_ok. rewrite lb_small_lbl, nlarge_lbl, <- length_lbl.
  rewrite (fold_perm _ _ _ P), (fold_perm (fun x => nlg (snd x)) _ _ P), (Permutation_length P).
  cbn [fold_right snd length]. unfold nsmall, nlg, po_small, po_cnt, po_large. cbn -[Z.div].
  assert (0 <= n / 2) by (apply Z.div_pos; lia). assert (0 <= n / 3) by (apply Z.div_pos; lia). lia.
Qed.

Lemma pm_phi_fresh : forall st words n, fresh_state st words n -> pm_phi (pmc_of st) = 0.
Proof.
  intros st words n FR. unfold pm_phi, pm_prog. rewrite (proj2 (fresh_blocks st words n FR)).
  destruct FR as (_ & _ & W0 & _). cbn [pmc_of c_widx]. rewrite W0. reflexivity.
Qed.

Lemma rdn_2_split : forall segs m (x : word) b0 b1, PropExec.rdn segs m x 2 = Some [b0; b1] ->
  PropExec.rdn segs m x 1 = Some [b0] /\ PropExec.rdn segs m (x + 1)%bv 1 = Some [b1].
Proof.
  intros segs m x b0 b1 R. cbn [PropExec.rdn] in *.
  destruct (match m x with Some b => Some b | None => PropExec.seg_rom segs x end) as [c0|]; [|discriminate].
  destruct (match m (x + 1)%bv with Some b => Some b | None => PropExec.seg_rom segs (x + 1)%bv end) as [c1|]; [|discriminate].
  injection R as -> ->. split; reflexivity.
Qed.

Lemma fld2_split0 : forall m a, 0 <= a -> a + 2 < 2 ^ 64 -> fld ASEGS m a 2 0 -> fld ASEGS m a 1 0 /\ fld ASEGS m (a + 1) 1 0.
Proof.
  intros m a H0 H1 F. unfold fld in *.
  change (word_to_le_bytes 2 (Z_to_bv 64 0)) with [Z_to_bv 8 0; Z_to_bv 8 0] in F.
  change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
  destruct (rdn_2_split ASEGS m _ _ _ F) as [F1 F2]. split; [exact F1|].
  replace (Z_to_bv 64 (a + 1)) with (Z_to_bv 64 a + 1)%bv; [exact F2|].
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_unsigned (1%bv : bv 64)) with 1.
  rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (a + 1)) by lia. reflexivity.
Qed.

Section World.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition pm_world (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z) : pmwA H :=
    PMWA H p (pc_cons c) (pc_user c) (st_diag (pc_state c)) (st_words (pc_state c)) (st_nwords (pc_state c))
         (bv_unsigned sp) (pmS1 (bv_unsigned sp)) ff fp (bv_unsigned ra)
         [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra] gp tp LB0 LF CH m0 mo0 st0 lo B shi.
End World.

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

  Definition pro_wins (spz ff fp : Z) : list (Z * Z) :=
    [(pmS1 spz - AFS_STACK, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 8); (sh ff, sh ff + fshn 8)].

  Lemma pmS1_facts : forall spz, 0 <= spz -> spz mod 16 = 0 -> spz - 1248 <= pmS1 spz <= spz - 1216 /\ pmS1 spz mod 32 = 0.
  Proof.
    intros spz H0 H16. unfold pmS1. pose proof (Z.mod_pos_bound (spz - 1216) 32 ltac:(lia)). split; [lia|].
    pose proof (Z.div_mod (spz - 1216) 32 ltac:(lia)). Z.div_mod_to_equations. lia.
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
    replace (sh AIMG_TOP) with 0x800d4c00 in * by reflexivity.
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

  Definition e2_wins (S1 ff : Z) : list (Z * Z) := [(S1 + 1056, S1 + 1064); (ff, ff + 24); (sh ff, sh ff + 1952)].

  Lemma aconst_ok_of : forall lo hi, (0x6e5908 <= lo /\ sh AIMG_TOP <= lo) \/ (0x6e5908 <= lo /\ hi <= 0x7fff7000) ->
    aconst_ok (lo, hi).
  Proof.
    intros lo hi HLO.
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
      AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
      replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d4c00 in * by reflexivity;
      destruct HLO as [(L1 & L2)|(L1 & L2)]; lia.
  Qed.

  Lemma e2_props : forall LF m spz ff fp LB, as_RFS H LF m -> fresh_frame H LF 8 ff fp -> aceil <= pmS1 spz - AFS_STACK ->
    pmS1 spz + 1064 <= spz ->
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
    replace (sh AIMG_TOP) with 0x800d4c00 in Q5 by reflexivity.
    split; [| split; [| split]].
    - unfold e2_wins. repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      + left. lia.
      + right; right; right; right; left. unfold AFS_HDR, AFS_SIZE in *. lia.
      + right; right; right; right; right; left. lia.
    - unfold e2_wins. repeat apply Forall_cons; try apply Forall_nil; apply aconst_ok_of.
      + left. replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity. lia.
      + destruct FB3 as [(L1 & L2)|(L1 & L2)].
        * right. unfold AIMG_TOP, AFS_HDR, AFS_SIZE, ALOWSH_LO in *. lia.
        * left. replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity. unfold AHI_LO, AFS_HDR in *. lia.
      + left. replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity. unfold AIMG_TOP in *. lia.
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

  Lemma pro_munch : forall spz ff fp m m1 m2, pmS1 spz + 1064 <= spz -> spz - 1248 <= pmS1 spz ->
    munch [(spz - 1216, spz); (pmS1 spz - AFS_STACK, pmS1 spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1);
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

  Lemma vec_opnd_init : forall s LB m v b, as_RHEAP H s LB m ->
    @vraw AC_A ASEGS LY_A MI_A (lbl LB) m v b b (b + 500) -> b <> 0 -> mdef m v 24 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    as_FSB H <= v /\ v + 24 <= as_FSB H + AFS_SIZE ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m v b 0 25.
  Proof.
    intros s LB m v b RH [Vb Ve Vc Vblk] Hb HD Hv Hv' Hdj.
    destruct Vblk as [(E & _)|(_ & HIn & _)]; [contradiction|].
    replace (b + 500 - b) with (OPND_SZ * 25) in HIn by (unfold OPND_SZ; lia).
    destruct (lbl_blk LB _ _ HIn) as (pid & Hin).
    pose proof (ah_blocks H HHi _ _ _ _ RH Hin) as (B0 & B16 & Bn & BT & Bc & BF & BA). cbn [blk_addr blk_size fst snd] in *.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold vec_opnd. unfold OPND_SZ in *. unfold AFS_SIZE in *.
    split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [lia|].
    split; [right; repeat split; try lia; exact HIn|].
    split; [exact (proj2 Vb)|]. split; [replace (b + 20 * 0) with b by lia; exact (proj2 Ve)|].
    replace (b + 20 * 25) with (b + 500) by lia. exact (proj2 Vc).
  Qed.

  Lemma vec32_init : forall s LB m v b, as_RHEAP H s LB m ->
    @vraw AC_A ASEGS LY_A MI_A (lbl LB) m v b b (b + 100) -> b <> 0 -> mdef m v 24 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    as_FSB H <= v /\ v + 24 <= as_FSB H + AFS_SIZE ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m v b [] 25.
  Proof.
    intros s LB m v b RH [Vb Ve Vc Vblk] Hb HD Hv Hv' Hdj.
    destruct Vblk as [(E & _)|(_ & HIn & _)]; [contradiction|].
    replace (b + 100 - b) with (4 * 25) in HIn by lia.
    destruct (lbl_blk LB _ _ HIn) as (pid & Hin).
    pose proof (ah_blocks H HHi _ _ _ _ RH Hin) as (B0 & B16 & Bn & BT & Bc & BF & BA). cbn [blk_addr blk_size fst snd] in *.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold vec32. unfold Zlen. cbn [length Z.of_nat]. unfold AFS_SIZE in *.
    split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [lia|].
    split; [right; repeat split; try lia; exact HIn|].
    split; [exact (proj2 Vb)|]. split; [replace (b + 4 * Z.of_nat 0) with b by lia; exact (proj2 Ve)|].
    split; [replace (b + 4 * 25) with (b + 100) by lia; exact (proj2 Vc)|].
    intros i Hi. lia.
  Qed.

  Lemma umapx_empty_disj : forall NS (V : Type) (nval : mem -> Z -> V -> Prop)
      (nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v)
      W LB m m' obj, 24 <= NS -> munch W m m' -> disjoint_from W obj 40 -> 0 <= obj -> obj + 40 < 2 ^ 64 ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m obj 0 0 [] -> @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m' obj 0 0 [].
  Proof.
    intros NS V nval nval_agree W LB m m' obj HNS MU D H0 H1 U.
    eapply (umapx_agree ASEGS LY_A MI_A NS V nval nval_agree HNS); [exact U | | intros p0 n0 _ Hl; exact Hl].
    intros a Ha. unfold umap_foot in Ha. destruct Ha as [Ha|[(Hbc & _)|(q & Hq & _)]]; [| lia | destruct Hq].
    apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia].
  Qed.

  Lemma e2_disj_stack : forall LF m spz ff fp a n, as_RFS H LF m -> fresh_frame H LF 8 ff fp ->
    pmS1 spz + 1064 <= a -> aceil <= a -> disjoint_from (e2_wins (pmS1 spz) ff) a n.
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

  Lemma pm_init : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBs : list block) (LF : list fframe) (CH : list (Z * Z)) (p : Z) (c : parserC)
           (lo B shi : Z) (errv : word) (Q : config -> Prop),
      let words := st_words (pc_state c) in let n := st_nwords (pc_state c) in
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 APM_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 p ->
      parser_repA LB m p c -> parser_sh m p c -> fsin LF p PARSER_SIZE -> fsin LF (pc_cons c) 48 -> pc_cons c mod 16 = 0 ->
      wr_at asegs m (pc_cons c) 48 ->
      fresh_state (pc_state c) words n ->
      0 <= n < 2 ^ 24 -> (words = 0 /\ n = 0) \/ words_okA LB0 m words n ->
      state_own LB LB0 LBs (pc_state c) -> lb_own LBs m ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_small LB0 + po_small n <= RT_SMALL_MAX -> Z.of_nat (length LB0) + po_cnt n <= RT_CNT_MAX ->
      nlarge LB0 + po_large n <= RT_LARGE_MAX ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->
      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - APM_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      LINV m -> ACONST m ->
      as_RFS H LF m -> (length LF + PM_FRAMES <= AFS_MAXLIVE_BP)%nat ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_chain H m (bv_unsigned s0) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pm_tr_ok H -> pf_ok (as_TR H) PM_PF (bv_unsigned ra) CH ->
      po_cost n <= as_AL H s ->
      (forall (ff fp : Z) msF1 mo1 m1 R1,
         let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c ff fp LB0 LF CH m mo s lo B shi in
         pmw_okA H w -> PMXA H LINV w s LB LBs m1 mo1 (pmc_of (pc_state c)) [] TBL_ED284 [] ->
         as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xed414) fc None m1 (seg_rom asegs) -> rfull R1 ->
         regs_tbl w R1 RT_ED284 -> PropExec.getr R1 3%bv = gp -> PropExec.getr R1 4%bv = tp ->
         as_SR H Q (mkCfg msF1 mo1)) ->
      as_SR H Q (mkCfg msF mo).
  Proof.
    intros until Q. intros words n VIS Ha0 PR PSH FIN CIN C16 CWR FRESH Hn WOK SOWN LBOWN RH KR MS1 MS2 MS3 RA SPB B64 SP16
           STK CE LO ERR MI TP RA2 LI AC RFS LFB S0 SPS CHN CHF HTR HPF ALC K.
    set (spz := bv_unsigned sp) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. fold spz in Hspr.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as (SB1 & SB2 & SB3).
    eapply (pm_e1 H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF p lo Q
              VIS KR Ha0 STK CE ltac:(unfold APM_STACK in LO; lia) SP16 ltac:(unfold AAPP_HI in *; lia) MI AC RH RFS ltac:(unfold PM_FRAMES in LFB; lia) TP).
    intros msF1 mo1 m1 ff fp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' KR1 MP1 VIS1 MU1 WM1 MI1 STK1 SAV1 RFS1 CL1 SH1 FLB1 AC1 RH1.
    pose proof (fresh_of_RFS H (HHi) _ _ _ _ _ RFS1) as FR.
    pose proof (fresh_frame_facts H _ _ _ _ FR) as (FK & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF3 & FF4 & FB1 & FB2 & FB3).
    change (fsz 8) with 16384 in *.
    assert (FAPP : aapp ff 16384) by (eapply aapp_sub; [exact FB3 | unfold AFS_HDR in *; lia | lia]).
    destruct FIN as (fP & HfP & PF1 & PF2).
    pose proof (proj2 (ah_RFS_range H HHi _ _ RFS) fP HfP) as (PK & PQ1 & PQ2 & _).
    pose proof PR as [PRcons PRuser PRhdr PRins PRhunk PRst PRdef PRal PRrange PRconsf PRconsm PRconsd].
    destruct PRrange as (P0 & P47).
    pose proof (fsz_pos (ff_class fP) (proj1 PK)) as FZP0.
    assert (P288 : p + 288 <= aceil) by (unfold PARSER_SIZE, AFS_SIZE in *; lia).
    eapply (pm_e2 H HHbp sp gp tp s2 s4 s5 s7 s8 s9 s10 s11 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc msF1 m1 mo1 s p ff fp lo Q
              VIS1 KR1 STK1 CE ltac:(unfold APM_STACK in LO; lia) SP16 ltac:(unfold AAPP_HI in *; lia) FF1 ltac:(change (fsz 8) with 16384; lia)
              FF64 ltac:(change (fsz 8) with 16384; exact FAPP) SH1 CL1 P0 P288 MI1).
    intros msF2 mo2 m2 R2 KR2 MP2 VIS2 RF2 MU2 WM2 MI2 STK2 FSH2 HDR2 SLOT2 G2 G8 G9 G18 G19 G20 G21 G22 G27 G26 G3 G4 G23 G24 G25.
    fold spz in MU1, SAV1, CL1, MU2, SLOT2, G2, G9.
    set (w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c ff fp LB0 LF CH m mo s lo B shi).
    destruct CIN as (fC & HfC & CF1 & CF2).
    pose proof (proj2 (ah_RFS_range H HHi _ _ RFS) fC HfC) as (CK & CQ1 & CQ2 & _).
    pose proof (fsz_pos (ff_class fP) (proj1 PK)) as FZP. pose proof (fsz_pos (ff_class fC) (proj1 CK)) as FZC.
    pose proof (pmS1_facts spz ltac:(lia) SP16) as (S1a & S1b).
    assert (OK : pmw_okA H w).
    { constructor; cbn [w pm_world wa_p wa_cons wa_user wa_diag wa_words wa_n wa_sp0 wa_s1 wa_ff wa_fp wa_ra wa_saved wa_gp wa_tp
                        wa_LB0 wa_LF0 wa_CH wa_m0 wa_mo0 wa_s0 wa_lo wa_B wa_shi]; fold spz.
      - exact FR.
      - right. exists fP. exact (conj HfP (conj PF1 PF2)).
      - exists fP. exact (conj HfP (conj PF1 PF2)).
      - split; [eapply aapp_sub; [exact FB3 | unfold AFS_HDR in *; lia | unfold PARSER_SIZE in *; lia] |]. split; [lia | exact PRal].
      - right. exists fC. exact (conj HfC (conj CF1 CF2)).
      - split; [eapply aapp_sub; [exact FB3 | unfold AFS_HDR in *; lia | lia] |]. split; [unfold AFS_HDR, AIMG_TOP in *; lia | exact C16].
      - unfold apart, PARSER_SIZE in *. exact PRconsd.
      - exists fC. exact (conj HfC (conj CF1 CF2)).
      - exact CHF.
      - exact (bv_unsigned_in_range_64 ra).
      - split; [exact MS1 |]. split; [exact MS2 | exact MS3].
      - unfold APM_STACK in *. repeat split; try lia.
      - exact (conj S1a S1b).
      - exact TP.
      - exact RFS.
      - exact WOK.
      - exact Hn.
      - reflexivity.
      - exact LFB.
      - exact B64.
      - destruct PRst as [_ _ SW2 _ _ _ _ _ _ _ _ _ _ _ _ _]. exact (proj1 SW2).
      - exact HTR.
      - exact HPF. }

    assert (HS : aceil <= pmS1 spz - AFS_STACK) by (unfold AFS_STACK, APM_STACK in *; lia).
    assert (H64 : pmS1 spz + 1064 <= spz) by lia.
    unfold APM_STACK in LO.
    assert (Hff : 0 <= ff /\ ff + 16384 < 2 ^ 47) by (unfold AIMG_TOP, AFS_HDR in FF1; lia).
    pose proof (pro_munch spz ff fp m m1 m2 H64 ltac:(lia) MU1 MU2) as MU.
    pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM.
    pose proof (e2_props LF m spz ff fp LB RFS FR HS H64) as (E2A & E2C & E2F & E2O).
    pose proof (pro_aclient LF m spz ff fp LB RFS FR HS) as PA.
    pose proof (pro_stack0 LF m spz ff fp RFS FR HS) as PS0.
    pose proof (pro_img LF m spz ff fp RFS FR HS) as PI.
    pose proof (pro_below LF m spz ff fp RFS FR HS ltac:(lia)) as PB.
    assert (Hc0 : 0 < pc_cons c) by (unfold AIMG_TOP, AFS_HDR in *; lia).
    assert (PAPP : aapp p PARSER_SIZE) by (eapply aapp_sub; [exact FB3 | unfold AFS_HDR in *; lia | unfold PARSER_SIZE in *; lia]).
    assert (CAPP : aapp (pc_cons c) 48) by (eapply aapp_sub; [exact FB3 | unfold AFS_HDR in *; lia | lia]).
    destruct (pro_obj LF m spz ff fp p PARSER_SIZE RFS FR HS (fsobj_inframe H LF fP p PARSER_SIZE HfP PF1 PF2) ltac:(lia)
                ltac:(unfold PARSER_SIZE; lia) PAPP) as [DP DPs].
    destruct (pro_obj LF m spz ff fp (pc_cons c) 48 RFS FR HS (fsobj_inframe H LF fC (pc_cons c) 48 HfC CF1 CF2) ltac:(lia)
                ltac:(lia) CAPP) as [DC DCs].
    assert (PF : forall k w0 v, 0 <= k -> k + Z.of_nat w0 <= PARSER_SIZE -> fld ASEGS m (p + k) w0 v -> fld ASEGS m2 (p + k) w0 v).
    { intros k w0 v Hk Hkw F0. eapply fld_disj; [exact MU | eapply disj_sub; [exact DP | lia | lia | lia] | lia | unfold PARSER_SIZE in *; lia | exact F0]. }

    destruct SOWN as [SO1 SO2].
    pose proof FRESH as (Fw & Fn & Fwi & Fic & Ffl & Fm1 & Fm2 & Fm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
    destruct (fresh_blocks _ _ _ FRESH) as [FBL1 FBL2].
    destruct PRst as [Sw0 Sw1 Sw2 Sw3 Sw4 Sw5 Sw6 Sm1 Sm2 Sm3 Sv1 Sv2 Sv3 Sdef Sal Snd]. unfold ST_OFF in *.
    destruct PSH as (PSp & PSc & (SHm1 & SHm2 & SHm3 & SHv1 & SHv2 & SHv3)).
    replace (p + 48 + 8) with (p + 56) in Sw1 by lia. replace (p + 48 + 16) with (p + 64) in Sw2 by lia.
    replace (p + 48 + 24) with (p + 72) in Sw3 by lia. replace (p + 48 + 32) with (p + 80) in Sw4 by lia.
    replace (p + 48 + 40) with (p + 88) in Sw5 by lia. replace (p + 48 + 44) with (p + 92) in Sw6 by lia.
    replace (p + 48 + 48) with (p + 96) in Sm1 by lia. replace (p + 48 + 88) with (p + 136) in Sm2 by lia.
    replace (p + 48 + 128) with (p + 176) in Sm3 by lia. replace (p + 48 + 168) with (p + 216) in Sv1 by lia.
    replace (p + 48 + 192) with (p + 240) in Sv2 by lia. replace (p + 48 + 216) with (p + 264) in Sv3 by lia.
    rewrite Fm1 in Sm1. rewrite Fm2 in Sm2. rewrite Fm3 in Sm3. cbn [t3a t3b t3c fst snd] in Sm1, Sm2, Sm3.
    rewrite <- E1, C1 in Sv1. rewrite <- E2, C2 in Sv2. rewrite <- E3, C3 in Sv3.
    assert (PDEF : mdef m p PARSER_SIZE).
    { intros i Hi. unfold PARSER_SIZE in Hi. destruct (Z.lt_ge_cases i 48); [apply PRdef; lia|].
      replace (p + i) with (p + 48 + (i - 48)) by lia. apply Sdef. lia. }
    assert (VDEF : forall k, 0 <= k -> k + 24 <= 240 -> mdef m (p + 48 + k) 24).
    { intros k Hk Hk2 i Hi. replace (p + 48 + k + i) with (p + 48 + (k + i)) by lia. apply Sdef. lia. }
    assert (PFS : as_FSB H <= p /\ p + PARSER_SIZE <= as_FSB H + AFS_SIZE) by (unfold AFS_HDR in *; lia).
    assert (XV1 : @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m2 (p + O_V1) (t3a (st_v1 (pc_state c))) 0 25).
    { unfold O_V1. eapply vec_opnd_frame; [eapply (vec_opnd_init s LB m); [exact RH | exact Sv1 | exact N1 | | lia | lia | ] |].
      - replace (p + 216) with (p + 48 + 168) by lia. apply VDEF; lia.
      - unfold PARSER_SIZE in *. lia.
      - unfold vec_opnd_fp. eapply agree_of_disj; [exact MU | eapply disj_sub; [exact DP | lia | unfold PARSER_SIZE; lia | lia] | lia | unfold PARSER_SIZE in *; lia]. }
    assert (XV2 : @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m2 (p + O_V2) (t3a (st_v2 (pc_state c))) [] 25).
    { unfold O_V2. eapply vec32_frame; [eapply (vec32_init s LB m); [exact RH | exact Sv2 | exact N2 | | lia | lia | ] |].
      - replace (p + 240) with (p + 48 + 192) by lia. apply VDEF; lia.
      - unfold PARSER_SIZE in *. lia.
      - pose proof (agree_of_disj _ m m2 (p + 240) 24 MU (disj_sub _ p PARSER_SIZE (p + 240) 24 DP ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(lia))
                      ltac:(lia) ltac:(unfold PARSER_SIZE in *; lia)) as AG.
        intros a [Ha|(_ & Ha)]; [exact (AG a Ha) | unfold zwin, Zlen in Ha; cbn [length Z.of_nat] in Ha; lia]. }
    assert (XV3 : @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m2 (p + O_V3) (t3a (st_v3 (pc_state c))) [] 25).
    { unfold O_V3. eapply vec32_frame; [eapply (vec32_init s LB m); [exact RH | exact Sv3 | exact N3 | | lia | lia | ] |].
      - replace (p + 264) with (p + 48 + 216) by lia. apply VDEF; lia.
      - unfold PARSER_SIZE in *. lia.
      - pose proof (agree_of_disj _ m m2 (p + 264) 24 MU (disj_sub _ p PARSER_SIZE (p + 264) 24 DP ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(lia))
                      ltac:(lia) ltac:(unfold PARSER_SIZE in *; lia)) as AG.
        intros a [Ha|(_ & Ha)]; [exact (AG a Ha) | unfold zwin, Zlen in Ha; cbn [length Z.of_nat] in Ha; lia]. }
    assert (XM1 : @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m2 (p + O_M1) 0 0 []).
    { unfold O_M1. eapply (umapx_empty_disj 24 Z (nval24 ASEGS) (nval24_agree ASEGS)); [lia | exact MU | | lia | unfold PARSER_SIZE in *; lia | exact Sm1].
      eapply disj_sub; [exact DP | lia | unfold PARSER_SIZE; lia | lia]. }
    assert (XM2 : @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m2 (p + O_M2) 0 0 []).
    { unfold O_M2. eapply (umapx_empty_disj 32 (Z * Z * Z) (nval32 ASEGS) (nval32_agree ASEGS)); [lia | exact MU | | lia | unfold PARSER_SIZE in *; lia | exact Sm2].
      eapply disj_sub; [exact DP | lia | unfold PARSER_SIZE; lia | lia]. }
    assert (XM3 : @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m2 (p + O_M3) 0 0 []).
    { unfold O_M3. eapply (umapx_empty_disj 24 Z (nval24 ASEGS) (nval24_agree ASEGS)); [lia | exact MU | | lia | unfold PARSER_SIZE in *; lia | exact Sm3].
      eapply disj_sub; [exact DP | lia | unfold PARSER_SIZE; lia | lia]. }

    assert (VSH : forall b n0 sbs, In (b, n0) (state_blocks (pc_state c)) -> Z.of_nat (length sbs) <= nsh n0 -> SHAD m b sbs -> SHAD m2 b sbs).
    { intros b n0 sbs Hin Hl SH. apply (Permutation_in _ (Permutation_sym SO2)) in Hin. destruct (lbl_blk LBs _ _ Hin) as (pid & Hin').
      assert (HinLB : In (pid, b, n0) LB) by (apply (Permutation_in _ (Permutation_sym SO1)); apply in_app_iff; right; exact Hin').
      destruct (pro_blk LF m spz ff fp s LB pid b n0 RFS FR HS RH HinLB) as [_ DBs].
      eapply SHAD_transport; [exact SH | exact MU | exact WM |]. eapply disj_sub; [exact DBs | lia | lia | lia]. }

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
      - unfold APM_STACK in *. lia.
      - lia.
      - rewrite !Z_to_bv_bv_unsigned.
        assert (EM : map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra]
                     = map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1] ++ [C8 s0; C8 ra]) by reflexivity.
        pose proof SAV2 as SV. rewrite EM in SV. apply rw_cells_app in SV. destruct SV as [_ SV].
        rewrite cells_size_mapC8 in SV. cbn [length] in SV. replace (spz - 104 + Z.of_nat (8 * 11)) with (spz - 16) in SV by lia. exact SV. }

    assert (FL : fld ASEGS m (p + 92) 2 0) by (pose proof (proj2 Sw6) as X; rewrite Ffl in X; exact X).
    destruct (fld2_split0 m (p + 92) ltac:(lia) ltac:(lia) FL) as [FL1 FL2]. replace (p + 92 + 1) with (p + 93) in FL2 by lia.

    assert (XA : PMXA H LINV w s LB LBs m2 mo2 (pmc_of (pc_state c)) [] TBL_ED284 []).
    { constructor; cbn [w pm_world wa_p wa_cons wa_user wa_diag wa_words wa_n wa_sp0 wa_s1 wa_ff wa_fp wa_ra wa_saved wa_gp wa_tp
                        wa_LB0 wa_LF0 wa_CH wa_m0 wa_mo0 wa_s0 wa_lo wa_B wa_shi]; fold spz.
      - exact (ah_RHEAP_frame H HHi s LB m1 m2 _ RH1 MU2 WM2 E2A).
      - exact (lb_own_wmono _ _ _ LBOWN WM).
      - split; [apply lb_own_nil | cbn [length]; lia].
      - split; [rewrite app_nil_r; exact SO1 | rewrite FBL2, <- FBL1; exact SO2].
      - exact (fresh_meas LBs (pc_state c) words n FRESH SO2 ltac:(lia)).
      - exact (ah_mpres_trans H HHi _ _ _ MP1 MP2).
      - exact MI2.
      - exact STK2.
      - exists errv. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. apply disj_low; [exact PI |].
        rewrite TP. rewrite unsigned_lit by (unfold ATP; lia). cbn [cells_size csize Nat.add]. unfold ATP, AIMG_TOP. lia.
      - exact (ah_rauxv_frame H HHi LB m m2 B _ RA MU WM PA).
      - exact (ACONST_frame _ m1 m2 AC1 MU2 WM2 E2C).
      - exact (stack0_transport _ m m2 lo shi S0 MU WM PS0).
      - exact (LINV_frame m m2 _ LI MU WM PI).
      - exact (ah_RFS_frame H HHi _ m1 m2 _ RFS1 MU2 WM2 E2F).
      - exists [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1)]. split.
        + pose proof (fs_scratch_of_fresh H LF 8 ff fp FR) as FS.
          apply Forall_cons; [exact (Forall_inv FS) | apply Forall_cons; [exact (Forall_inv (Forall_inv_tail FS)) | apply Forall_nil]].
        + eapply (xpres_weaken H LB LB0 spz spz ((p, p + PARSER_SIZE) :: (ff, ff + fsz PM_FCLASS) :: (sh ff, sh ff + fshn PM_FCLASS)
                                                   :: [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1)]));
            [| lia | | intros a Ha; right; exact Ha].
          * eapply (xpres_of_munch H s LB); [exact HHi | exact RH | exact MU | exact WM | exact (pro_xp LF m spz ff fp p RFS FR HS)].
          * intros b Hb. apply (Permutation_in _ (Permutation_sym SO1)). apply in_app_iff. left. exact Hb.
      - rewrite (pm_phi_fresh _ _ _ FRESH). split; [lia|].
        split; [unfold pm_cap; rewrite (proj2 (fresh_blocks _ _ _ FRESH)); unfold pm_phi_blocks, ICM_LARGE, PM_RESERVE, po_cost; cbn [fold_right snd];
                replace (64512 <? 500) with false by reflexivity; replace (64512 <? 100) with false by reflexivity; lia|].
        split; [exact ALC | unfold PM_RESERVE; lia].
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
      - apply (PF 48 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact (proj2 Sw0)].
      - apply (PF 56 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact (proj2 Sw1)].
      - apply (PF 64 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact (proj2 Sw2)].
      - apply (PF 72 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact (proj2 Sw3)].
      - apply (PF 80 8%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact (proj2 Sw4)].
      - apply (PF 88 4%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact (proj2 Sw5)].
      - cbn [pmc_of c_reqconv]. rewrite Ffl. apply (PF 92 1%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact FL1].
      - replace (p + O_FLAGS + 1) with (p + 93) by (unfold O_FLAGS; lia). apply (PF 93 1%nat); [lia | unfold PARSER_SIZE; cbn; lia | exact FL2].
      - cbn [pmc_of c_widx c_icount c_endian c_reqconv]. rewrite Fwi, Fic, Ffl.
        pose proof (proj1 Sw5) as R5. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in R5. lia.
      - eapply fld_disj; [exact MU | eapply disj_sub; [exact DC | lia | cbn; lia | lia] | lia | cbn; lia | exact PRconsf].
      - eapply mdef_disj; [exact MU | eapply disj_sub; [exact DC | lia | lia | lia] | lia | lia | exact PRconsm].
      - exact (wr_at_wmono _ _ _ _ CWR WM).
      - intros Hwz. destruct WOK as [[E0 _]|(pw & k & Hin & Hk & W0 & W16 & Whi & Wdef & Wsh)]; [exfalso; apply Hwz; exact E0|].
        assert (HinLB : In (pw, words, k) LB) by (apply (Permutation_in _ (Permutation_sym SO1)); apply in_app_iff; left; exact Hin).
        destruct (pro_blk LF m spz ff fp s LB pw words k RFS FR HS RH HinLB) as [DW _].
        eapply mdef_disj; [exact MU | eapply disj_sub; [exact DW | lia | lia | lia] | lia | lia | exact Wdef].
      - cbn [pmc_of c_m1]. rewrite Fm1. exact XM1.
      - cbn [pmc_of c_m2]. rewrite Fm2. exact XM2.
      - cbn [pmc_of c_m3]. rewrite Fm3. exact XM3.
      - exact XV1.
      - exact XV2.
      - exact XV3.
      - split; [| split].
        + unfold pmc_sh. cbn [pmc_of c_m1 c_m2 c_m3 c_v1 c_v2 c_v3]. rewrite Fm1, Fm2, Fm3.
          assert (UE : forall NS (V : Type), umap_sh m2 NS ((0, 0, []) : Z * Z * list (Z * (Z * V)))).
          { intros NS V. split; [intros Hbc; exfalso; apply Hbc; reflexivity | intros q k v Hin; destruct Hin]. }
          split; [apply UE|]. split; [apply UE|]. split; [apply UE|].
          unfold vec_sh in SHv1, SHv2, SHv3. rewrite <- E1, C1 in SHv1. rewrite <- E2, C2 in SHv2. rewrite <- E3, C3 in SHv3.
          split; [| split].
          * unfold vsh_opnd. cbn [t3a t3b t3c fst snd]. intros Hb. pose proof (SHv1 N1) as X.
            replace (t3a (st_v1 (pc_state c)) + 500 - t3a (st_v1 (pc_state c))) with 500 in X by lia.
            replace (t3a (st_v1 (pc_state c)) - t3a (st_v1 (pc_state c))) with 0 in X by lia.
            change (OPND_SZ * 25) with 500. change (OPND_SZ * 0) with 0.
            apply (VSH _ 500); [rewrite FBL1; left; reflexivity | rewrite cc_gen_length by lia; lia | exact X].
          * unfold vsh32. cbn [t3a t3b t3c fst snd]. intros Hb. pose proof (SHv2 N2) as X.
            replace (t3a (st_v2 (pc_state c)) + 100 - t3a (st_v2 (pc_state c))) with 100 in X by lia.
            replace (t3a (st_v2 (pc_state c)) - t3a (st_v2 (pc_state c))) with 0 in X by lia.
            change (4 * 25) with 100. change (4 * Zlen []) with 0.
            apply (VSH _ 100); [rewrite FBL1; right; left; reflexivity | rewrite cc_gen_length by lia; lia | exact X].
          * unfold vsh32. cbn [t3a t3b t3c fst snd]. intros Hb. pose proof (SHv3 N3) as X.
            replace (t3a (st_v3 (pc_state c)) + 100 - t3a (st_v3 (pc_state c))) with 100 in X by lia.
            replace (t3a (st_v3 (pc_state c)) - t3a (st_v3 (pc_state c))) with 0 in X by lia.
            change (4 * 25) with 100. change (4 * Zlen []) with 0.
            apply (VSH _ 100); [rewrite FBL1; right; right; left; reflexivity | rewrite cc_gen_length by lia; lia | exact X].
        + exact (addressable_transport _ m m2 p PARSER_SIZE PSp MU WM DPs).
        + exact (addressable_transport _ m m2 (pc_cons c) 48 PSc MU WM DCs). }

    assert (RT : regs_tbl w R2 RT_ED284).
    { unfold regs_tblX, RT_ED284. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - rewrite G2. reflexivity.
      - rewrite G8. transitivity (Z_to_bv 64 spz); [subst spz; symmetry; apply Z_to_bv_bv_unsigned | reflexivity].
      - rewrite G9. reflexivity.
      - rewrite G18. reflexivity.
      - rewrite G19. reflexivity.
      - rewrite G20. symmetry. apply sh_expr_val; [reflexivity | reflexivity | lia].
      - rewrite G21. symmetry. transitivity (alu64 ALU_ADD (Z_to_bv 64 p) (Z_to_bv 64 48)); [reflexivity | apply w_add; lia].
      - rewrite G22. reflexivity.
      - rewrite G26. symmetry. apply sh_expr_val; [| reflexivity | lia].
        transitivity (alu64 ALU_ADD (Z_to_bv 64 p) (Z_to_bv 64 48)); [reflexivity | apply w_add; lia].
      - rewrite G27. reflexivity. }
    exact (K ff fp msF2 mo2 m2 R2 OK XA KR2 VIS2 RF2 RT G3 G4).
  Qed.
End Init.
