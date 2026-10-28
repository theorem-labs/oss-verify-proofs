(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmDS LbB_WoGen LbB_ContStmt LbB_PmWKit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition V4_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section WG.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.

  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.

  Hypothesis HOWN : rt_own H.

  Lemma HHw : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma mdef_hdrs : forall (p : Z) (m' : mem) L1 L2 L3 L4 L5 L6 a1 b1 e1 a2 b2 e2 a3 b3 e3 x1 y1 z1 x2 y2 z2 x3 y3 z3,
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L1 m' (p + O_M1) a1 b1 e1 ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L2 m' (p + O_M2) a2 b2 e2 ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L3 m' (p + O_M3) a3 b3 e3 ->
    @vec_opnd AC_A ASEGS LY_A MI_A L4 m' (p + O_V1) x1 y1 z1 ->
    @vec32 AC_A ASEGS LY_A MI_A L5 m' (p + O_V2) x2 y2 z2 ->
    @vec32 AC_A ASEGS LY_A MI_A L6 m' (p + O_V3) x3 y3 z3 ->
    mdef m' (p + O_M1) (PARSER_SIZE - O_M1).
  Proof.
    intros p m' L1 L2 L3 L4 L5 L6 a1 b1 e1 a2 b2 e2 a3 b3 e3 x1 y1 z1 x2 y2 z2 x3 y3 z3 U1 U2 U3 V1 V2 V3.
    pose proof (h_def (u_hdr U1)) as D1. pose proof (h_def (u_hdr U2)) as D2. pose proof (h_def (u_hdr U3)) as D3.
    pose proof V1 as (_ & _ & D4 & _). pose proof V2 as (_ & _ & D5 & _). pose proof V3 as (_ & _ & D6 & _).
    intros i Hi. unfold O_M1, PARSER_SIZE in Hi.
    destruct (Z_lt_le_dec i 40) as [L1'|L1']; [| destruct (Z_lt_le_dec i 80) as [L2'|L2']; [| destruct (Z_lt_le_dec i 120) as [L3'|L3'];
      [| destruct (Z_lt_le_dec i 144) as [L4'|L4']; [| destruct (Z_lt_le_dec i 168) as [L5'|L5']]]]].
    - replace (p + O_M1 + i) with (p + O_M1 + i) by reflexivity. exact (D1 i ltac:(lia)).
    - replace (p + O_M1 + i) with (p + O_M2 + (i - 40)) by (unfold O_M1, O_M2; lia). exact (D2 (i - 40) ltac:(lia)).
    - replace (p + O_M1 + i) with (p + O_M3 + (i - 80)) by (unfold O_M1, O_M3; lia). exact (D3 (i - 80) ltac:(lia)).
    - replace (p + O_M1 + i) with (p + O_V1 + (i - 120)) by (unfold O_M1, O_V1; lia). exact (D4 (i - 120) ltac:(lia)).
    - replace (p + O_M1 + i) with (p + O_V2 + (i - 144)) by (unfold O_M1, O_V2; lia). exact (D5 (i - 144) ltac:(lia)).
    - replace (p + O_M1 + i) with (p + O_V3 + (i - 168)) by (unfold O_M1, O_V3; lia). exact (D6 (i - 168) ltac:(lia)).
  Qed.

  Lemma xpres_img : forall LBk SP X m m', xpres H LBk SP X m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) X ->
    forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a).
  Proof.
    intros LBk SP X m m' XP FX a Ha HC. apply (XP a Ha). split; [right; left; exact HC|].
    intros R. unfold aimg_client in HC. clear - FX R HC. induction X as [|iv X IH]; cbn in R; [contradiction|].
    apply Forall_cons_iff in FX as [F1 F2]. destruct R as [R|R]; [cbn beta in F1; unfold AIMG_TOP in F1; lia | exact (IH F2 R)].
  Qed.

  Lemma scratch_above : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> AIMG_TOP <= fst iv.
  Proof.
    intros LF m iv R [->|(k & ff & fp & FF & E)].
    - cbn [fst]. destruct (proj1 (ah_RFS_range H HHw _ _ R)) as (F1 & F2 & F3 & F4). lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      destruct E as [-> |[-> | ->]]; cbn [fst]; [unfold AFS_HDR in *; lia | unfold AFS_FLAGS in *; lia |].
      pose proof (sh_mono AIMG_TOP ff ltac:(unfold AFS_HDR in *; lia)). replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold AIMG_TOP. lia.
  Qed.
  Lemma scratch_img : forall (w : pmwA H) m XS, as_RFS H (PMLF H w) m -> Forall (fs_scratch H (PMLF H w)) XS ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) XS.
  Proof. intros w m XS R FXS. eapply Forall_impl; [| exact FXS]. intros iv Hiv. exact (scratch_above _ _ _ R Hiv). Qed.

  Definition vx (w : pmwA H) (ho : Z) (b n : Z) : list (Z * Z) := (wa_p w + ho, wa_p w + ho + 24) :: v4_oldx b n.

  Lemma vx_vwin : forall w ho b n, 0 <= n -> Forall (vwin H w ho (b, n)) (vx w ho b n).
  Proof.
    intros w ho b n Hn. unfold vx, v4_oldx. apply Forall_cons.
    - split; [cbn [fst snd]; lia|]. left. cbn [fst snd]. lia.
    - destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      + split; [cbn [fst snd]; lia|]. right; left. cbn [fst snd]. lia.
      + split; [cbn [fst snd]; unfold nsh; Z.div_mod_to_equations; lia|]. right; right. cbn [fst snd]. lia.
  Qed.

  Lemma vx_img : forall w s LB m ho b n pid, pmw_okA H w -> as_RHEAP H s LB m -> 0 <= ho -> (b <> 0 -> In (pid, b, n) LB) ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) (vx w ho b n).
  Proof.
    intros w s LB m ho b n pid OK RH Hho Hin. pose proof (p_range H w OK) as [PR1 _].
    unfold vx, v4_oldx. apply Forall_cons; [cbn [fst]; lia|].
    destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
    pose proof (ah_blocks H HHw _ _ _ _ RH (Hin E)) as (R0 & R16 & Rn & RI & _). cbn [blk_addr blk_size fst snd] in *.
    apply Forall_cons; [cbn [fst]; lia|]. apply Forall_cons; [cbn [fst] | apply Forall_nil].
    pose proof (sh_mono AIMG_TOP b ltac:(lia)). replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold AIMG_TOP. lia.
  Qed.

  Lemma pmxa_keep_but_xp : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' (L' : list (Z * Z)) X XS (ho : Z) (xb : Z * Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_RFS H (PMLF H w) m' -> Forall (fs_scratch H (PMLF H w)) XS ->
    xpres H LB (wa_s1 w) (X ++ XS) m m' -> Forall (vwin H w ho xb) X ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> vsel c ho xb ->
    (forall q, In q (c_blocks c) -> q <> xb -> In q (lbl LB) -> In q L') ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L' m' (wa_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L' m' (wa_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L' m' (wa_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
    /\ umap_sh m' 24 (c_m1 c) /\ umap_sh m' 32 (c_m2 c) /\ umap_sh m' 24 (c_m3 c)
    /\ (ho <> O_V1 -> @vec_opnd AC_A ASEGS LY_A MI_A L' m' (wa_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) /\ vsh_opnd m' (c_v1 c))
    /\ (ho <> O_V2 -> @vec32 AC_A ASEGS LY_A MI_A L' m' (wa_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) /\ vsh32 m' (c_v2 c))
    /\ (ho <> O_V3 -> @vec32 AC_A ASEGS LY_A MI_A L' m' (wa_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) /\ vsh32 m' (c_v3 c)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' L' X XS ho xb OK X0 RFS' FXS XP FW HO1 HO2 SEL LIVE.
    pose proof HHw as HH.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (p_range H w OK) as [PR1 PR2].
    destruct (p_frame H HH w OK) as (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4). unfold AFS_HDR in PF3.
    assert (BLK : forall q, In q (c_blocks c) -> In q (lbl LB) /\ 0 < fst q /\ fst q + snd q <= aceil /\ AIMG_TOP <= fst q /\ 0 <= snd q /\ fst q mod 16 = 0
                                                /\ exists pid, In (pid, fst q, snd q) LB).
    { intros [A n] Hin. destruct (xb_facts H HH w s LB LBs TB m c (A, n) OK RH OWN1 OWN2 Hin) as (pid & _ & A2 & A3 & (R0 & R16 & Rn & RI & RC & _)).
      cbn [fst snd] in *. split; [exact A3|]. split; [exact R0|]. split; [exact RC|]. split; [exact RI|]. split; [exact Rn|]. split; [exact R16|]. exists pid. exact A2. }
    assert (XBc : fst xb <> 0 -> In xb (c_blocks c)).
    { intros NZ. unfold c_blocks. rewrite !in_app_iff.
      destruct SEL as [(E & ->)|[(E & ->)|(E & ->)]]; unfold blkV1, blkV2, blkV3 in *; cbn [fst] in NZ.
      - right; right; right; left. unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [contradiction | left; reflexivity].
      - right; right; right; right; left. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [contradiction | left; reflexivity].
      - right; right; right; right; right; left. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [contradiction | left; reflexivity]. }
    assert (XB : fst xb <> 0 -> In xb (lbl LB)) by (intros NZ; exact (proj1 (BLK xb (XBc NZ)))).
    assert (FW' : Forall (fun iv => sown H w iv \/ vwin H w ho xb iv) X) by (eapply Forall_impl; [| exact FW]; intros iv Hiv; right; exact Hiv).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    assert (FOp : fsobj H (PMLF H w) (wa_p w) PARSER_SIZE) by (right; exists fp0; split; [right; exact Hfp0 | lia]).
    pose proof (xp_scr_obj H HH w m' XS (wa_p w) PARSER_SIZE OK RFS' FXS FOp ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia) PA) as [SXp _].
    assert (SXb : forall pid A n, In (pid, A, n) LB ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XS /\ Forall (fun iv : Z * Z => sh A + nsh n <= fst iv \/ snd iv <= sh A) XS).
    { intros pid A n Hin. pose proof (ah_blocks H HH _ _ _ _ RH Hin) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
      assert (FO : fsobj H (PMLF H w) A n) by (eapply fsobj_block; [exact HH | exact RH | exact Hin]).
      exact (xp_scr_obj H HH w m' XS A n OK RFS' FXS FO ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP). }
    apply (pmc_keep_but (wa_p w) (lbl LB) L' m m' c ho xb
             (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
             (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
             (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)));
      [lia | unfold PARSER_SIZE in *; lia
      | exact (cblocks_nodup H HH s LB (wa_LB0 w) LBs TB m c RH OWN1 OWN2) | intros q Hq; exact (proj1 (proj2 (BLK q Hq))) | exact SEL | | | | exact LIVE].
    -
      intros a Ha AH. unfold wa. apply (XP a ltac:(unfold O_M1, PARSER_SIZE in Ha; lia)).
      eapply (xclient_range_addr H LB (wa_s1 w) (X ++ XS) a 1); [| lia]. split.
      + right; right; right; right; left. unfold O_M1, PARSER_SIZE in *. lia.
      + apply Forall_app. split.
        * eapply Forall_impl; [| exact FW']. intros iv Hiv.
          apply (vsw_apart_p H HH w s LB m ho xb iv a 1 OK RH XB HO1 HO2 Hiv); unfold O_M1, PARSER_SIZE in *; lia.
        * eapply Forall_impl; [| exact SXp]. intros iv Hiv. cbn beta in Hiv. unfold O_M1, PARSER_SIZE in *. lia.
    -
      intros A n a Hin Hne Ha. destruct (BLK _ Hin) as (HinL & B0 & BC & BI & Bn & B16 & (pid & HinLB)). cbn [fst snd] in *.
      apply (XP a ltac:(lia)). eapply (xclient_range_addr H LB (wa_s1 w) (X ++ XS) a 1); [| lia]. split.
      + right; right; left. exists (pid, A, n). split; [exact HinLB|]. cbn [blk_addr blk_size fst snd]. lia.
      + apply Forall_app. split.
        * eapply Forall_impl; [| exact FW']. intros iv Hiv.
          apply (vsw_apart_blk H HH w s LB m ho xb iv A n a 1 OK RH XB HO1 HO2 Hiv HinL Hne); lia.
        * eapply Forall_impl; [| exact (proj1 (SXb pid A n HinLB))]. intros iv Hiv. cbn beta in Hiv. lia.
    -
      intros A n sbs Hin Hne Hlen SH. destruct (BLK _ Hin) as (HinL & B0 & BC & BI & Bn & B16 & (pid & HinLB)). cbn [fst snd] in *.
      eapply (xpres_SHAD H); [exact XP | exact SH |]. split.
      + right; right; right; left. exists (pid, A, n). split; [exact HinLB|]. cbn [blk_addr blk_size fst snd]. lia.
      + apply Forall_app. split.
        * eapply Forall_impl; [| exact FW']. intros iv Hiv.
          apply (vsw_apart_blksh H HH w s LB m ho xb iv A n (sh A) _ OK RH XB HO1 HO2 Hiv HinL Hne); lia.
        * eapply Forall_impl; [| exact (proj2 (SXb pid A n HinLB))]. intros iv Hiv. cbn beta in Hiv. lia.
  Qed.

  Lemma pmxa_vgrow_gen : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' (c' : pmc) (ho : Z)
      (pid pid' : bptr) (b n b' n' loss : Z) (PRE POST XS : list (Z * Z)),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE ->
    c_blocks c = PRE ++ (if b =? 0 then [] else [(b, n)]) ++ POST ->
    c_blocks c' = PRE ++ [(b', n')] ++ POST ->
    (b <> 0 -> In (pid, b, n) LBs) -> 0 <= n ->
    pm_bud (wa_n w) c' -> pm_phi c' >= pm_phi c + loss ->
    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->

    as_RHEAP H s' (v4_newLB H LB b pid pid' b' n') m' -> as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) ->
    as_rauxv_ok H m' (wa_B w) ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LB (wa_s1 w) (vx w ho b n ++ XS) m m' ->
    ablock_range H b' n' -> wr_at asegs m' (wa_p w + ho) 24 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s - loss ->

    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl (v4_newLB H LB b pid pid' b' n')) m' (wa_p w + O_M1) (t3a (c_m1 c')) (t3b (c_m1 c')) (t3c (c_m1 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl (v4_newLB H LB b pid pid' b' n')) m' (wa_p w + O_M2) (t3a (c_m2 c')) (t3b (c_m2 c')) (t3c (c_m2 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl (v4_newLB H LB b pid pid' b' n')) m' (wa_p w + O_M3) (t3a (c_m3 c')) (t3b (c_m3 c')) (t3c (c_m3 c')) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl (v4_newLB H LB b pid pid' b' n')) m' (wa_p w + O_V1) (t3a (c_v1 c')) (t3b (c_v1 c')) (t3c (c_v1 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl (v4_newLB H LB b pid pid' b' n')) m' (wa_p w + O_V2) (t3a (c_v2 c')) (t3b (c_v2 c')) (t3c (c_v2 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl (v4_newLB H LB b pid pid' b' n')) m' (wa_p w + O_V3) (t3a (c_v3 c')) (t3b (c_v3 c')) (t3c (c_v3 c')) ->
    pmc_sh m' c' ->
    PMXAT H LINV w s' (v4_newLB H LB b pid pid' b' n') ((pid', b', n') :: (if b =? 0 then LBs else as_lb_remove H pid LBs))
          m' mo' c' ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' c' ho pid pid' b n b' n' loss PRE POST XS
           OK X0 Hknn Hfk HO1 HO2 CB CB' PIDin Hn BUDc PG Cw Ci Ce Cr
           RH' MP' MI' STK' ERR' RA' FXS XP ABR' WR' RFS' AC' S0' AL' U1 U2 U3 V1 V2 V3 SHc.
    pose proof HHw as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_n H w OK) as WN.
    set (LB' := v4_newLB H LB b pid pid' b' n') in *.
    set (LBs' := (pid', b', n') :: (if b =? 0 then LBs else as_lb_remove H pid LBs)).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (ah_nodup H HH _ _ _ RH) as ND.
    assert (NDs : List.NoDup (map blk_id LBs)).
    { pose proof (Permutation_NoDup (Permutation_map blk_id OWN1) ND) as ND2. rewrite !map_app in ND2.
      apply nodup_app_r in ND2. exact (nodup_app_l _ _ ND2). }
    assert (OLDf : b <> 0 -> In (pid, b, n) LB /\ ablock_range H b n).
    { intros NZ. pose proof (PIDin NZ) as I1.
      assert (I2 : In (pid, b, n) LB).
      { apply (Permutation_in _ (Permutation_sym OWN1)). apply in_or_app; right. apply in_or_app; left. exact I1. }
      split; [exact I2|]. exact (proj2 (lbs_blk H HH w s LB LBs TB m _ RH OWN1 I1)). }

    assert (P1 : Permutation LB' (wa_LB0 w ++ LBs' ++ TB)).
    { unfold LB', LBs', v4_newLB. destruct (Z.eqb_spec b 0) as [E|E].
      - apply own_grow0. exact OWN1.
      - apply (own_grow H HH LB (wa_LB0 w) LBs TB pid pid' b n b' n' ND OWN1 (PIDin E)). }
    assert (P2 : Permutation (lbl LBs') (c_blocks c')).
    { unfold LBs'. rewrite CB'. rewrite CB in OWN2.
      apply (cblocks_grow H HH LBs PRE POST pid pid' b n b' n' NDs OWN2). intros NZ. exact (PIDin NZ). }
    assert (MEAS' : pm_meas_ok (wa_n w) LBs') by (apply (pm_meas_of_bud (wa_n w) c' LBs'); [lia | exact BUDc | exact P2]).

    pose proof (HOWN s' LB' m' RH') as OWNall.
    assert (OWN3 : lb_own LBs' m').
    { eapply lb_own_incl; [| exact OWNall]. intros bb Hbb. apply (Permutation_in _ (Permutation_sym P1)).
      apply in_or_app; right. apply in_or_app; left. exact Hbb. }
    assert (TBO : lb_own TB m').
    { eapply lb_own_incl; [| exact OWNall]. intros bb Hbb. apply (Permutation_in _ (Permutation_sym P1)).
      apply in_or_app; right. apply in_or_app; right. exact Hbb. }
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [_ TBL].

    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    assert (RESV' : pm_cap c' + PM_RESERVE <= po_cost (wa_n w)) by (apply pm_resv_of_bud; [exact WN | exact BUDc]).

    assert (FX : Forall (xv_ok4 H w LBs ftbl) (vx w ho b n)).
    { unfold vx, v4_oldx. apply Forall_cons.
      - right; left. cbn [fst snd]. clear - HO1 HO2. unfold O_M1, O_V1, PARSER_SIZE in *. lia.
      - destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
        pose proof (OLDf E) as [_ (R0 & R16 & Rn & _)].
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
        + right; right; left. cbn [fst snd]. split; [lia|]. exists (pid, b, n). split; [exact (PIDin E)|]. cbn [blk_addr blk_size fst snd]. lia.
        + right; right; right. cbn [fst snd]. split; [unfold nsh; Z.div_mod_to_equations; lia|].
          exists (pid, b, n). split; [exact (PIDin E)|]. cbn [blk_addr blk_size fst snd]. lia. }
    assert (FXW : Forall (fun iv : Z * Z => (snd iv <= wa_ff w + 24 \/ wa_ff w + 16376 <= fst iv) \/ wr_at asegs m' (fst iv) (snd iv - fst iv)) (vx w ho b n)).
    { unfold vx, v4_oldx. apply Forall_cons.
      - right. cbn [fst snd]. replace (wa_p w + ho + 24 - (wa_p w + ho)) with 24 by lia. exact WR'.
      - destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
        pose proof (OLDf E) as [INb ABRb]. pose proof (blk_apart_ff H HH w s LB m _ OK RH INb) as AP. cbn [blk_addr blk_size fst snd] in AP.
        pose proof ABRb as (R0 & R16 & Rn & RI & RC & RF & RAPP).
        pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; left; cbn [fst snd].
        + change (fsz PM_FCLASS) with 16384 in AP. lia.
        +
          destruct RAPP as [(L1 & L2)|(L1 & L2)]; destruct FA as [(M1 & M2)|(M1 & M2)]; unfold aapp_lo, aapp_hi in *.
          * right. unfold sh, ASHADOW_BASE, ALOWSH_LO, AIMG_TOP in *. Z.div_mod_to_equations. lia.
          * left. assert (sh (b + n) <= sh ALOWSH_LO) by (apply sh_mono; lia).
            assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
            replace (sh ALOWSH_LO) with 0x8fff6e00 in * by reflexivity. unfold AHI_LO in *. lia.
          * right. assert (sh AHI_LO <= sh b) by (apply sh_mono; lia).
            replace (sh AHI_LO) with 0x2008fff7000 in * by reflexivity. unfold ALOWSH_LO in *. lia.
          * left. assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
            assert (sh (b + n) <= sh aceil) by (apply sh_mono; lia).
            assert (sh aceil + 1 <= AHI_LO) by (unfold sh, ASHADOW_BASE, AHI_LO; Z.div_mod_to_equations; lia). lia. }

    assert (MDh : mdef m' (wa_p w + O_M1) (PARSER_SIZE - O_M1)) by (eapply mdef_hdrs; [exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3]).

    eapply (pmxa_xv4 H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB spal LB (vx w ho b n) XS);
      [exact OK | exact X0 | exact Hknn | exact RH' | exact MP' | exact MI' | exact STK' | exact ERR' | exact RA' | exact RFS' | exact AC' | exact S0'
      | apply (LINV_cl m m' (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)); eapply xpres_img; [exact XP | apply Forall_app; split; [exact (vx_img w s LB m ho b n pid OK RH ltac:(unfold O_V1 in HO1; lia) (fun NZ => proj1 (OLDf NZ))) | exact (scratch_img w m' XS RFS' FXS)]]
      | exact FXS | exact XP | exact FX | exact FXW | exact MDh | exact Hfk
      | intros bb Hbb; exact Hbb
      | intros bb Hbb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_or_app; left; exact Hbb
      | exact P1 | exact P2 | exact OWN3 | exact MEAS' | exact TBO | exact TBL
      | lia | exact RESV' | exact A4
      | exact Cw | exact Ci | exact Ce | exact Cr
      | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3 | exact SHc ].
  Qed.

  Lemma pmxa_vsame_gen : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' (c' : pmc) (ho : Z)
      (pid : bptr) (b n : Z) (XS : list (Z * Z)),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE ->
    c_blocks c' = c_blocks c -> (b <> 0 -> In (pid, b, n) LBs) -> 0 <= n ->
    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->

    as_RHEAP H s' LB m' -> as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) ->
    as_rauxv_ok H m' (wa_B w) ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LB (wa_s1 w) (vx w ho b n ++ XS) m m' ->
    wr_at asegs m' (wa_p w + ho) 24 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M1) (t3a (c_m1 c')) (t3b (c_m1 c')) (t3c (c_m1 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m' (wa_p w + O_M2) (t3a (c_m2 c')) (t3b (c_m2 c')) (t3c (c_m2 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M3) (t3a (c_m3 c')) (t3b (c_m3 c')) (t3c (c_m3 c')) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V1) (t3a (c_v1 c')) (t3b (c_v1 c')) (t3c (c_v1 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V2) (t3a (c_v2 c')) (t3b (c_v2 c')) (t3c (c_v2 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V3) (t3a (c_v3 c')) (t3b (c_v3 c')) (t3c (c_v3 c')) ->
    pmc_sh m' c' ->
    PMXAT H LINV w s' LB LBs m' mo' c' ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' c' ho pid b n XS
           OK X0 Hknn Hfk HO1 HO2 CB' PIDin Hn Cw Ci Ce Cr
           RH' MP' MI' STK' ERR' RA' FXS XP WR' RFS' AC' S0' AL' U1 U2 U3 V1 V2 V3 SHc.
    pose proof HHw as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    assert (OLDf : b <> 0 -> In (pid, b, n) LB /\ ablock_range H b n).
    { intros NZ. pose proof (PIDin NZ) as I1.
      assert (I2 : In (pid, b, n) LB).
      { apply (Permutation_in _ (Permutation_sym OWN1)). apply in_or_app; right. apply in_or_app; left. exact I1. }
      split; [exact I2|]. exact (proj2 (lbs_blk H HH w s LB LBs TB m _ RH OWN1 I1)). }
    assert (P2 : Permutation (lbl LBs) (c_blocks c')) by (rewrite CB'; exact OWN2).
    pose proof (HOWN s' LB m' RH') as OWNall.
    assert (OWN3 : lb_own LBs m').
    { eapply lb_own_incl; [| exact OWNall]. intros bb Hbb. apply (Permutation_in _ (Permutation_sym OWN1)).
      apply in_or_app; right. apply in_or_app; left. exact Hbb. }
    assert (TBO : lb_own TB m').
    { eapply lb_own_incl; [| exact OWNall]. intros bb Hbb. apply (Permutation_in _ (Permutation_sym OWN1)).
      apply in_or_app; right. apply in_or_app; right. exact Hbb. }
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [_ TBL].
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    assert (PHI : pm_phi c' = pm_phi c) by (unfold pm_phi, pm_prog; rewrite CB', Cw; reflexivity).
    assert (PCP : pm_cap c' = pm_cap c) by (unfold pm_cap; rewrite CB'; reflexivity).
    assert (FX : Forall (xv_ok4 H w LBs ftbl) (vx w ho b n)).
    { unfold vx, v4_oldx. apply Forall_cons.
      - right; left. cbn [fst snd]. clear - HO1 HO2. unfold O_M1, O_V1, PARSER_SIZE in *. lia.
      - destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
        pose proof (OLDf E) as [_ (R0 & R16 & Rn & _)].
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
        + right; right; left. cbn [fst snd]. split; [lia|]. exists (pid, b, n). split; [exact (PIDin E)|]. cbn [blk_addr blk_size fst snd]. lia.
        + right; right; right. cbn [fst snd]. split; [unfold nsh; Z.div_mod_to_equations; lia|].
          exists (pid, b, n). split; [exact (PIDin E)|]. cbn [blk_addr blk_size fst snd]. lia. }
    assert (FXW : Forall (fun iv : Z * Z => (snd iv <= wa_ff w + 24 \/ wa_ff w + 16376 <= fst iv) \/ wr_at asegs m' (fst iv) (snd iv - fst iv)) (vx w ho b n)).
    { unfold vx, v4_oldx. apply Forall_cons.
      - right. cbn [fst snd]. replace (wa_p w + ho + 24 - (wa_p w + ho)) with 24 by lia. exact WR'.
      - destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
        pose proof (OLDf E) as [INb ABRb]. pose proof (blk_apart_ff H HH w s LB m _ OK RH INb) as AP. cbn [blk_addr blk_size fst snd] in AP.
        pose proof ABRb as (R0 & R16 & Rn & RI & RC & RF & RAPP).
        pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; left; cbn [fst snd].
        + change (fsz PM_FCLASS) with 16384 in AP. lia.
        + destruct RAPP as [(L1 & L2)|(L1 & L2)]; destruct FA as [(M1 & M2)|(M1 & M2)]; unfold aapp_lo, aapp_hi in *.
          * right. unfold sh, ASHADOW_BASE, ALOWSH_LO, AIMG_TOP in *. Z.div_mod_to_equations. lia.
          * left. assert (sh (b + n) <= sh ALOWSH_LO) by (apply sh_mono; lia).
            assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
            replace (sh ALOWSH_LO) with 0x8fff6e00 in * by reflexivity. unfold AHI_LO in *. lia.
          * right. assert (sh AHI_LO <= sh b) by (apply sh_mono; lia).
            replace (sh AHI_LO) with 0x2008fff7000 in * by reflexivity. unfold ALOWSH_LO in *. lia.
          * left. assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
            assert (sh (b + n) <= sh aceil) by (apply sh_mono; lia).
            assert (sh aceil + 1 <= AHI_LO) by (unfold sh, ASHADOW_BASE, AHI_LO; Z.div_mod_to_equations; lia). lia. }
    assert (MDh : mdef m' (wa_p w + O_M1) (PARSER_SIZE - O_M1)) by (eapply mdef_hdrs; [exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3]).
    eapply (pmxa_xv4 H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal s' LB LBs m' mo' c' TB spal LB (vx w ho b n) XS);
      [exact OK | exact X0 | exact Hknn | exact RH' | exact MP' | exact MI' | exact STK' | exact ERR' | exact RA' | exact RFS' | exact AC' | exact S0'
      | apply (LINV_cl m m' (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)); eapply xpres_img; [exact XP | apply Forall_app; split; [exact (vx_img w s LB m ho b n pid OK RH ltac:(unfold O_V1 in HO1; lia) (fun NZ => proj1 (OLDf NZ))) | exact (scratch_img w m' XS RFS' FXS)]]
      | exact FXS | exact XP | exact FX | exact FXW | exact MDh | exact Hfk
      | intros bb Hbb; exact Hbb
      | intros bb Hbb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_or_app; left; exact Hbb
      | exact OWN1 | exact P2 | exact OWN3 | exact (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact TBO | exact TBL
      | rewrite PHI; lia | rewrite PCP; exact A2 | exact A4
      | exact Cw | exact Ci | exact Ce | exact Cr
      | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3 | exact SHc ].
  Qed.

  Lemma vgrow_live : forall (w : pmwA H) s LB LBs TB m c (pid pid' : bptr) (b n b' n' : Z) (xb : Z * Z) q,
    pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) -> Permutation (lbl LBs) (c_blocks c) ->
    xb = (b, n) -> (b <> 0 -> In (pid, b, n) LBs) ->
    In q (c_blocks c) -> q <> xb -> In q (lbl LB) -> In q (lbl (v4_newLB H LB b pid pid' b' n')).
  Proof.
    intros w s LB LBs TB m c pid pid' b n b' n' xb [A k] OK RH OWN1 OWN2 -> PIDin Hq Hne Hl.
    unfold v4_newLB, lbl. cbn [map fst snd]. right. fold (lbl LB). fold (lbl (as_lb_remove H pid LB)).
    destruct (Z.eqb_spec b 0) as [E|E]; [exact Hl|].
    destruct (xb_facts H HHw w s LB LBs TB m c (A, k) OK RH OWN1 OWN2 Hq) as (qid & Q1 & Q2 & _). cbn [fst snd] in *.
    apply (lbl_in _ qid). apply (lb_remove_keep H HHw pid LB (qid, A, k) (ah_nodup H HHw _ _ _ RH) Q2).
    cbn [blk_id fst]. intros EQ. subst qid.

    pose proof (PIDin E) as P0.
    assert (NDs : List.NoDup (map blk_id LBs)).
    { pose proof (Permutation_NoDup (Permutation_map blk_id OWN1) (ah_nodup H HHw _ _ _ RH)) as ND2. rewrite !map_app in ND2.
      apply nodup_app_r in ND2. exact (nodup_app_l _ _ ND2). }
    pose proof (nodup_map_inj blk_id LBs (pid, b, n) (pid, A, k) NDs P0 Q1 eq_refl) as EQ. injection EQ as <- <-. apply Hne. reflexivity.
  Qed.

  Lemma vx_ff_keep : forall (w : pmwA H) s LB m m1 ho b n (pid : bptr) XS k cs,
    pmw_okA H w -> as_RHEAP H s LB m -> as_RFS H (PMLF H w) m1 -> Forall (fs_scratch H (PMLF H w)) XS ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> (b <> 0 -> In (pid, b, n) LB) -> 0 <= n ->
    xpres H LB (wa_s1 w) (vx w ho b n ++ XS) m m1 -> 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
    rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs.
  Proof.
    intros w s LB m m1 ho b n pid XS k cs OK RH RF1 FXS HO1 HO2 PIDin Hn XP1 Hk Hkc RWk. pose proof HHw as HH.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    eapply (ff_cells_xpres H HHbp w m m1 LB (vx w ho b n) XS k cs OK RF1 FXS);
      [exact XP1 | | exact Hk | exact Hkc | exact RWk].
    destruct (p_frame H HH w OK) as (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4).
    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF. change (fsz PM_FCLASS) with 16384 in PFF.
    unfold vx, v4_oldx. apply Forall_cons; [cbn [fst snd]; unfold O_V1, PARSER_SIZE in *; lia|].
    destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil|].
    pose proof (PIDin E) as INb.
    pose proof (blk_apart_ff H HH w s LB m _ OK RH INb) as AP. cbn [blk_addr blk_size fst snd] in AP. change (fsz PM_FCLASS) with 16384 in AP.
    pose proof (ah_blocks H HH _ _ _ _ RH INb) as (R0 & R16 & Rn & RI & RC & RFb & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RFb, RAPP.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd] | apply Forall_nil].
    destruct RAPP as [(L1 & L2)|(L1 & L2)]; destruct FA as [(N1 & N2)|(N1 & N2)]; unfold aapp_lo, aapp_hi in *.
    - left. unfold sh, ASHADOW_BASE, ALOWSH_LO, AIMG_TOP in *. Z.div_mod_to_equations. lia.
    - right. assert (sh (b + n) <= sh ALOWSH_LO) by (apply sh_mono; lia).
      assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
      replace (sh ALOWSH_LO) with 0x8fff6e00 in * by reflexivity. unfold AHI_LO in *. lia.
    - left. assert (sh AHI_LO <= sh b) by (apply sh_mono; lia).
      replace (sh AHI_LO) with 0x2008fff7000 in * by reflexivity. unfold ALOWSH_LO in *. lia.
    - right. assert (sh b + nsh n <= sh (b + n) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
      assert (sh (b + n) <= sh aceil) by (apply sh_mono; lia).
      assert (sh aceil + 1 <= AHI_LO) by (unfold sh, ASHADOW_BASE, AHI_LO; Z.div_mod_to_equations; lia). lia.
  Qed.
End WG.
