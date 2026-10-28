(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_VecD1 LbB_Own LbB_MILB
  LbB_PrsStmt LbB_HKit LbB_HStKit LbB_StateStmt LbB_HStDtL LbB_HStDtK LbB_HStDtV LbB_HStDtM.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma hdr3_of_umapx : forall NS V (nval : mem -> Z -> V -> Prop) A M o bl bc (ents : list (Z * (Z * V))),
  umapx MI_A NS nval A M o bl bc ents -> AIMG_TOP <= o ->
  rw_cells asegs M o [C8 (wz bl); C8 (wz bc); C8 (wz (hdaddr ents))].
Proof.
  intros NS V nval A M o bl bc ents U Ho. pose proof (u_hdr U) as [Hbl Hbc Hp1 _ _ _].
  pose proof (u_obj_hi U) as OH. pose proof Ho as Ho'. unfold AIMG_TOP in Ho'.
  change [C8 (wz bl); C8 (wz bc); C8 (wz (hdaddr ents))] with ([C8 (wz bl)] ++ [C8 (wz bc)] ++ [C8 (wz (hdaddr ents))]).
  apply rw_cells_app. split; [apply rw_cells_of_cellw8; [exact Hbl | exact Ho | lia]|].
  replace (o + Z.of_nat (cells_size [C8 (wz bl)])) with (o + 8) by (cbn; lia).
  apply rw_cells_app. split.
  - apply rw_cells_of_cellw8; [exact Hbc | unfold AIMG_TOP; lia | lia].
  - replace (o + 8 + Z.of_nat (cells_size [C8 (wz bc)])) with (o + 16) by (cbn; lia).
    apply rw_cells_of_cellw8; [exact Hp1 | unfold AIMG_TOP; lia | lia].
Qed.

Lemma vec_blk_cases : forall (Ak : list block) (v : Z * Z * Z), lbl Ak = vec_blocks v ->
  (t3a v = 0 /\ Ak = []) \/ (t3a v <> 0 /\ exists pid, Ak = [(pid, t3a v, t3c v - t3a v)]).
Proof.
  intros Ak v E. unfold vec_blocks in E. destruct (Z.eqb_spec (t3a v) 0) as [Z0|NZ].
  - left. split; [exact Z0|]. destruct Ak; [reflexivity | discriminate E].
  - right. split; [exact NZ|]. destruct Ak as [|[[pid a] n] Ak']; [discriminate E|].
    unfold lbl in E. cbn [map fst snd] in E. injection E as Ea En Er.
    destruct Ak'; [|discriminate Er]. exists pid. rewrite Ea, En. reflexivity.
Qed.

Lemma bkt_blk_cases : forall (Ak : list block) (bl bc : Z), lbl Ak = (if bc =? 0 then [] else [(bl, 8 * bc)]) ->
  (bc = 0 /\ Ak = []) \/ (bc <> 0 /\ exists qb, Ak = [(qb, bl, 8 * bc)]).
Proof.
  intros Ak bl bc E. destruct (Z.eqb_spec bc 0) as [Z0|NZ].
  - left. split; [exact Z0|]. destruct Ak; [reflexivity | discriminate E].
  - right. split; [exact NZ|]. destruct Ak as [|[[qb a] n] Ak']; [discriminate E|].
    unfold lbl in E. cbn [map fst snd] in E. injection E as Ea En Er.
    destruct Ak'; [|discriminate Er]. exists qb. rewrite Ea, En. reflexivity.
Qed.

Lemma lbl_split_eq : forall (LBs : list block) (l1 l2 : list (Z * Z)),
  lbl LBs = l1 ++ l2 -> exists L1 L2, Permutation LBs (L1 ++ L2) /\ lbl L1 = l1 /\ lbl L2 = l2.
Proof. intros LBs l1 l2 E. apply LbB_HMvaT.lbl_perm_split. rewrite E. apply Permutation_refl. Qed.

Lemma split6 : forall (LBs : list block) (c : stateC), Permutation (lbl LBs) (state_blocks c) ->
  exists X1 X2 X3 X4 X5 X6, Permutation LBs (X1 ++ X2 ++ X3 ++ X4 ++ X5 ++ X6)
    /\ lbl X1 = cb_m1 c /\ lbl X2 = cb_m2 c /\ lbl X3 = cb_m3 c /\ lbl X4 = cb_v1 c /\ lbl X5 = cb_v2 c /\ lbl X6 = cb_v3 c.
Proof.
  intros LBs c P. rewrite state_blocks_cb in P.
  destruct (LbB_HMvaT.lbl_perm_split LBs _ _ P) as (X1 & R1 & P1 & E1 & F1).
  destruct (lbl_split_eq R1 _ _ F1) as (X2 & R2 & P2 & E2 & F2).
  destruct (lbl_split_eq R2 _ _ F2) as (X3 & R3 & P3 & E3 & F3).
  destruct (lbl_split_eq R3 _ _ F3) as (X4 & R4 & P4 & E4 & F4).
  destruct (lbl_split_eq R4 _ _ F4) as (X5 & X6 & P5 & E5 & F5).
  exists X1, X2, X3, X4, X5, X6. split; [|tauto].
  eapply Permutation_trans; [exact P1|]. apply Permutation_app_head.
  eapply Permutation_trans; [exact P2|]. apply Permutation_app_head.
  eapply Permutation_trans; [exact P3|]. apply Permutation_app_head.
  eapply Permutation_trans; [exact P4|]. apply Permutation_app_head. exact P5.
Qed.

Lemma rw_cells3_split : forall m A x y z, rw_cells asegs m A [C8 x; C8 y; C8 z] ->
  rw_cells asegs m A [C8 x; C8 y] /\ rw_cells asegs m (A + 16) [C8 z].
Proof.
  intros m A x y z K. change [C8 x; C8 y; C8 z] with ([C8 x; C8 y] ++ [C8 z]) in K. apply rw_cells_app in K as [K1 K2].
  split; [exact K1|]. replace (A + 16) with (A + Z.of_nat (cells_size [C8 x; C8 y])) by (cbn; lia). exact K2.
Qed.

Lemma inZ_of_existsb : forall (x : Z) (l : list Z), existsb (Z.eqb x) l = true -> In x l.
Proof.
  intros x l. induction l as [|y l IH]; cbn [existsb]; [discriminate|].
  intros Hb. apply orb_true_iff in Hb as [Hb|Hb]; [left; symmetry; apply Z.eqb_eq; exact Hb | right; exact (IH Hb)].
Qed.

Lemma rin_ivs_dec : forall X a, {rin_ivs X a} + {~ rin_ivs X a}.
Proof.
  induction X as [|[l h] X IH]; intros a; cbn [rin_ivs fst snd]; [right; intros []|].
  destruct (Z_le_dec l a) as [H1|H1]; [destruct (Z_lt_dec a h) as [H2|H2]|].
  - left. left. lia.
  - destruct (IH a) as [K|K]; [left; right; exact K | right; intros [K'|K']; [lia | exact (K K')]].
  - destruct (IH a) as [K|K]; [left; right; exact K | right; intros [K'|K']; [lia | exact (K K')]].
Qed.
Lemma wr_in_ivs : forall m X a, Forall (fun iv : Z * Z => wr_at asegs m (fst iv) (snd iv - fst iv)) X -> rin_ivs X a ->
  wview asegs m (wa a) <> None.
Proof.
  intros m X a HX. induction HX as [|[l h] X Hw HX IH]; cbn [rin_ivs fst snd]; [intros []|].
  intros [Ha|Ha]; [|exact (IH Ha)].
  destruct Hw as (W0 & W1 & W). cbn [fst snd] in W. replace a with (l + (a - l)) by lia. apply W. lia.
Qed.
Lemma wr_at_of_defined : forall m a n, defined m a n -> 0 <= a -> a + n <= 2 ^ 64 -> wr_at asegs m a n.
Proof.
  intros m a n D H0 H1. split; [lia|]. split; [lia|]. intros i Hi. pose proof (D i Hi) as Di.
  unfold wview, wa. destruct (m (Z_to_bv 64 (a + i))) as [b|] eqn:E; [discriminate | contradiction].
Qed.

Lemma wr_one : forall m a b n, wr_at asegs m a n -> b - a = n ->
  Forall (fun iv : Z * Z => wr_at asegs m (fst iv) (snd iv - fst iv)) [(a, b)].
Proof. intros m a b n W E. constructor; [cbn [fst snd]; rewrite E; exact W | constructor]. Qed.

Section NodesXp.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma nodes_okG_xp : forall NS LBn ns LBk SP X m m', 8 <= NS ->
    nodes_okG NS LBn m ns -> xpres H LBk SP X m m' -> (forall b, In b LBn -> In b LBk) ->
    (forall b, In b LBn -> Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) X) ->
    (forall b, In b LBn -> forall a, sh (blk_addr b) <= a < sh (blk_addr b) + nsh (blk_size b) -> ~ rin_ivs X a) ->
    nodes_okG NS LBn m' ns.
  Proof.
    intros NS. induction LBn as [|b LBn IH]; intros ns LBk SP X m m' HNS NO XP INC HXc HXs; destruct ns as [|[q tl] ns];
      cbn [nodes_okG] in NO |- *; try tauto.
    destruct b as [[id A] n]. destruct NO as (BA & BS & CQ & ADQ & NXR & NO').
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS |- *. subst A n.
    assert (INB : In (id, q, NS) LBk) by (apply INC; left; reflexivity).
    split; [reflexivity|]. split; [reflexivity|]. split.
    - eapply (xpres_rw_cells H); [exact XP | exact CQ |]. cbn [cells_size csize]. rewrite ?Nat2Z.inj_add, ?Z2Nat.id by lia.
      cbn [Z.of_nat]. replace (Z.pos (Pos.of_succ_nat 7) + (NS - 8)) with NS by lia. split.
      + right; right; left. exists (id, q, NS). split; [exact INB | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia].
      + pose proof (HXc (id, q, NS) (or_introl eq_refl)) as K. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in K. eapply Forall_impl; [|exact K]. intros [l h] Hl. cbn [Datatypes.fst Datatypes.snd] in *. lia.
    - split.
      + eapply (addressable_xp H); [exact XP | exact ADQ |]. intros a Ha. split.
        * right; right; right; left. exists (id, q, NS). split; [exact INB | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia].
        * apply (HXs (id, q, NS) (or_introl eq_refl) a). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]. lia.
      + split; [exact NXR|]. eapply IH; [exact HNS | exact NO' | exact XP | intros b Hb; apply INC; right; exact Hb | |].
        * intros b Hb. apply HXc. right. exact Hb.
        * intros b Hb. apply HXs. right. exact Hb.
  Qed.
End NodesXp.

Section StDt.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (spz : Z).
  Variables (st : Z) (c : stateC) (LB0 : list block) (LF : list fframe) (lo B shi : Z) (errv : word).
  Variables (m0 : mem) (mo0 : Model) (sk0 : as_St H).

  Variables (vb3 ve3 vc3 vb2 ve2 vc2 vb1 ve1 vc1 : Z) (vp3 vp2 vp1 : bptr) (V3 V2 V1 : list block).
  Variables (mb3 mc3 mb2 mc2 mb1 mc1 : Z) (mq3 mq2 mq1 : bptr) (M3b M3n M2b M2n M1b M1n : list block).
  Variables (mn3 mn2 mn1 : list (Z * list byte)).

  Definition spf : Z := spz - 48.
  Definition L9 : list block := M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1 ++ V2 ++ V3.

  Definition DENV : Prop :=
    asan_rt_hyps H /\ annotate_gen_stmt /\ (forall n, as_Cf H n = 0)
    /\ frm_zero fc /\ spz mod 16 = 0 /\ (2 ^ 45 <= spz - 48 /\ spz <= 2 ^ 47)
    /\ (aceil <= lo /\ lo <= spz - AST_DTOR_STACK) /\ (spz <= shi /\ shi <= AAPP_HI) /\ spz <= B
    /\ tp = Z_to_bv 64 ATP /\ bv_unsigned ra mod 2 = 0 /\ st_dtor_tr_ok H /\ 0 <= as_AL H sk0
    /\ (st_live_frame LF st \/ (spz <= st /\ st + ST_SIZE + 64 <= shi))
    /\ st mod 8 = 0 /\ addressable m0 st ST_SIZE
    /\ (AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ as_FSB H mod 4096 = 0 /\ aapp (as_FSB H) AFS_SIZE)
    /\ (forall f, In f LF -> 0 <= ff_class f <= 10 /\ as_FSB H + AFS_HDR <= ff_addr f /\ ff_addr f + fsz (ff_class f) <= as_FSB H + AFS_SIZE)
    /\ (L9 <> [] -> st + ST_SIZE <= aceil)
    /\ (forall b, In b L9 -> st + 240 <= blk_addr b \/ blk_addr b + blk_size b <= st).

  Ltac denv DE :=
    destruct DE as (HH & HANN & HCF & FRZ & SP16 & SPR & LOH & SHH & SPB & TPV & RAE & TRS & AL0 & LOC & STA & HAD & FSBOK & LFR
                    & STC & BAP).

  Lemma st_where : DENV ->
    (as_FSB H <= st /\ st + 240 <= as_FSB H + AFS_SIZE /\ exists f, In f LF /\ ff_addr f <= st /\ st + ST_SIZE <= ff_addr f + fsz (ff_class f))
    \/ (spz <= st /\ st + 240 + 64 <= shi).
  Proof.
    intros DE. denv DE.
    destruct LOC as [(f & INF & F1 & F2)|K]; [left|right; unfold ST_SIZE in K; exact K].
    pose proof (LFR f INF) as (L0 & L1 & L2). pose proof (fsz_pos (ff_class f) ltac:(lia)). unfold AFS_HDR, ST_SIZE in *.
    split; [lia|]. split; [lia|]. exists f. split; [exact INF|]. unfold ST_SIZE. lia.
  Qed.
  Lemma st_bounds : DENV -> 0x6e6000 <= st /\ st + 240 <= 2 ^ 47 /\ (st + 240 <= spf \/ spz <= st)
                    /\ (st + 240 <= 0x7fff7000 \/ 0x10007fff8000 <= st).
  Proof.
    intros DE. pose proof (st_where DE) as W. denv DE.
    pose proof aceil_facts as ((AC1 & AC2) & _ & _). pose proof FSBOK as (FB1 & FB2 & FB3 & FB4).
    unfold AST_DTOR_STACK, AFREE_STACK, AAPP_HI, AIMG_TOP, AFS_SIZE, spf in *.
    destruct W as [(W1 & W2 & _)|(W1 & W2)].
    - unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AFS_SIZE in FB4, W2. lia.
    - unfold AHI_LO. lia.
  Qed.

  Lemma st_xcr : forall LBk SP X o n, DENV -> SP <= spz -> 0 <= o -> o + n <= 240 ->
    Forall (fun iv : Z * Z => st + o + n <= fst iv \/ snd iv <= st + o) X -> xclient_range H LBk SP X (st + o) n.
  Proof.
    intros LBk SP X o n DE HSP Ho Hn HX. split; [|exact HX].
    destruct (st_where DE) as [(W1 & W2 & _)|(W1 & W2)].
    - right; right; right; right; left. lia.
    - left. lia.
  Qed.

  Lemma st_sh_xc : forall LBk SP X a, DENV -> SP <= spz -> sh st <= a < sh st + 30 ->
    Forall (fun iv : Z * Z => st <= fst iv /\ snd iv <= st + 240) X -> xclient H LBk SP X a.
  Proof.
    intros LBk SP X a DE HSP Ha HX. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). pose proof (st_where DE) as W.
    denv DE. pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    assert (SB : ASHADOW_BASE <= sh st) by (unfold sh; pose proof (Z.div_pos st 8); lia).
    assert (SN : sh st + 30 <= AHI_LO) by (pose proof (sh_nsh_high st 240 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as K; change (nsh 240) with 30 in K; exact K).
    split.
    - destruct W as [(W1 & W2 & _)|(W1 & W2)].
      + right; right; right; right; right; left.
        assert (E1 : sh (as_FSB H) <= sh st) by (unfold sh; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
        assert (E2 : sh st + 30 <= sh (as_FSB H + AFS_SIZE)) by (clear - W2 STA; unfold sh, AFS_SIZE in *; Z.div_mod_to_equations; lia).
        lia.
      + right; right; right; right; right; right.
        assert (E1 : sh aceil <= sh st) by (unfold sh; apply Z.add_le_mono_l; apply Z.div_le_mono; destruct LOH as [LL1 LL2]; unfold AST_DTOR_STACK, AFREE_STACK in LL2; lia).
        lia.
    - clear - HX Ha SB SN B4. induction X as [|[l h] X IH]; [cbn; tauto|]. cbn [rin_ivs fst snd].
      pose proof (Forall_inv HX) as K1. cbn [fst snd] in K1. pose proof (Forall_inv_tail HX) as K2.
      unfold ASHADOW_BASE, AHI_LO in *. intros [K|K]; [lia | exact (IH K2 K)].
  Qed.

  Lemma st_wr_keep : forall LBk SP X (m m' : mem), DENV -> SP <= spz -> xpres H LBk SP X m m' ->
    Forall (fun iv : Z * Z => wr_at asegs m' (fst iv) (snd iv - fst iv)) X ->
    wr_at asegs m st 240 -> wr_at asegs m' st 240.
  Proof.
    intros LBk SP X m m' DE HSP XP WX (W0 & W1 & WH). pose proof (st_where DE) as WHR. clear DE.
    split; [exact W0|]. split; [exact W1|]. intros i Hi.
    destruct (rin_ivs_dec X (st + i)) as [RIN|NRIN]; [exact (wr_in_ivs m' X (st + i) WX RIN)|].
    assert (CL : aclient_addr H LBk SP (st + i)).
    { unfold aclient_addr. destruct WHR as [(K1 & K2 & _)|(K1 & K2)]; [right; right; right; right; left; lia | left; lia]. }
    destruct (XP (st + i) ltac:(lia) (conj CL NRIN)) as [_ WM]. apply WM. exact (WH i Hi).
  Qed.

  Definition INV (s : as_St H) (LBc : list block) (m : mem) (X : list (Z * Z)) (L : list block) : Prop :=
    mem_inv asegs m /\ stk asegs m lo spz /\ rw_cells asegs m (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m B
    /\ ACONST m /\ as_RFS H LF m /\ stack0 m lo shi /\ as_RHEAP H s LBc m /\ lb_own LBc m
    /\ rw_cells asegs m (spf + 16) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ Permutation LBc (LB0 ++ L)
    /\ xpres H LBc spz X m0 m
    /\ Forall (fun iv : Z * Z => st <= fst iv /\ snd iv <= st + 240) X
    /\ as_AL H s >= as_AL H sk0
    /\ wr_at asegs m st 240.

  Lemma INV_step : forall SPx s LBc m X L s' LBc' m' Xw L', DENV -> spf <= SPx <= spf + 16 ->
    INV s LBc m X L ->
    xpres H LBc' SPx Xw m m' -> (forall b, In b LBc' -> In b LBc) ->
    Forall (fun iv : Z * Z => st <= fst iv /\ snd iv <= st + 240) Xw ->
    mem_inv asegs m' -> stk asegs m' lo SPx -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
    ACONST m' -> as_RFS H LF m' -> stack0 m' lo shi -> as_RHEAP H s' LBc' m' -> lb_own LBc' m' ->
    as_AL H s' >= as_AL H s ->
    Permutation LBc' (LB0 ++ L') ->
    Forall (fun iv : Z * Z => wr_at asegs m' (fst iv) (snd iv - fst iv)) Xw ->
    INV s' LBc' m' (X ++ Xw) L'.
  Proof.
    intros SPx s LBc m X L s' LBc' m' Xw L' DE HSP INV0 XP INC FXw MI' ST' ERR' RA' AC' RF' S0' RH' OWN' AL' PE' WX.
    pose proof DE as DE0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    destruct INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP0 & FX & AL & WST).
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2].
    unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    assert (XF : Forall (fun iv : Z * Z => spz <= fst iv \/ snd iv <= spf) Xw).
    { eapply Forall_impl; [|exact FXw]. intros [l h] [K1 K2]. cbn [fst snd] in *. unfold spf in *. lia. }
    assert (FR' : rw_cells asegs m' (spf + 16) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (xpres_rw_cells H); [exact XP | exact FR |]. split; [left; lia|].
      cbn [cells_size csize Z.of_nat]. eapply Forall_impl; [|exact XF]. intros [l h] K. cbn [fst snd] in *. unfold spf in *. lia. }
    assert (STU : stk asegs m' SPx spz).
    { eapply (xpres_stk H); [exact XP | exact (proj2 (stk_split asegs m lo SPx spz ST ltac:(unfold spf in *; lia))) | unfold spf in *; lia |].
      eapply Forall_impl; [|exact XF]. intros [l h] K. cbn [fst snd] in *. lia. }
    split; [exact MI'|]. split; [exact (stk_merge asegs m' lo SPx spz ST' STU ltac:(unfold spf in *; lia))|].
    split; [exact ERR'|]. split; [exact RA'|]. split; [exact AC'|]. split; [exact RF'|]. split; [exact S0'|].
    split; [exact RH'|]. split; [exact OWN'|]. split; [exact FR'|]. split; [exact PE'|].
    split.
    { eapply (xpres_trans H).
      - eapply (xpres_weaken H); [exact XP0 | lia | exact INC |]. intros a Ha. rewrite rin_ivs_app. left. exact Ha.
      - eapply (xpres_weaken H); [exact XP | unfold spf in *; lia | intros b Hb; exact Hb |]. intros a Ha. rewrite rin_ivs_app. right. exact Ha. }
    split; [apply Forall_app; split; [exact FX | exact FXw]|]. split; [lia|].
    exact (st_wr_keep LBc' SPx Xw m m' DE0 ltac:(unfold spf in *; lia) XP WX WST).
  Qed.

  Definition vcomp (o k vb ve vc : Z) (vp : bptr) (Vb : list block) : Prop :=
    rw_cells asegs m0 (st + o) [C8 (wz vb); C8 (wz ve); C8 (wz vc)]
    /\ (vb = 0 -> ve = 0 /\ vc = 0)
    /\ ((vb = 0 /\ Vb = []) \/ (vb <> 0 /\ Vb = [(vp, vb, vc - vb)]))
    /\ (vb <> 0 -> vb <= ve <= vc /\ vc - vb <= 2 ^ 40 /\ SHAD m0 vb (cc_gen (vc - vb) (ve - vb)))
    /\ (vb <> 0 -> (ve - vb) mod k = 0).
  Definition mcomp (NS o mb mc : Z) (mq : bptr) (Mb Mn : list block) (mn : list (Z * list byte)) : Prop :=
    rw_cells asegs m0 (st + o) [C8 (wz mb); C8 (wz mc); C8 (wz (hdq mn))]
    /\ nodes_okG NS Mn m0 mn
    /\ ((mb = 0 /\ Mb = []) \/ (mb <> 0 /\ Mb = [(mq, mb, 8 * mc)] /\ addressable m0 mb (8 * mc)))
    /\ (mn = [] <-> Mn = []).
  Definition DCOMP : Prop :=
    vcomp 216 4 vb3 ve3 vc3 vp3 V3 /\ vcomp 192 4 vb2 ve2 vc2 vp2 V2 /\ vcomp 168 20 vb1 ve1 vc1 vp1 V1
    /\ mcomp 24 128 mb3 mc3 mq3 M3b M3n mn3 /\ mcomp 32 88 mb2 mc2 mq2 M2b M2n mn2 /\ mcomp 24 48 mb1 mc1 mq1 M1b M1n mn1.

  Definition QF : config -> Prop :=
    st_dtor_post H ra (Z_to_bv 64 spz) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sk0 LB0 LF st lo B shi m0 mo0.

  Lemma tr_of : forall r, DENV -> In r ST_DTOR_DEL_RAS -> trace_ok (as_TR H) APC0_FREE [r].
  Proof. intros r DE Hr. denv DE. unfold st_dtor_tr_ok in TRS. rewrite Forall_forall in TRS. exact (TRS r Hr). Qed.

  Lemma st_addr : forall o k, DENV -> 0 <= o -> o mod 8 = 0 -> k mod 8 = 0 -> 0 <= k -> o + k <= 240 -> addressable m0 (st + o) k.
  Proof.
    intros o k DE H0 H8 K8 K0 HK. denv DE. unfold ST_SIZE in HAD. clear - HAD H0 H8 K8 K0 HK.
    destruct (addressable_split8 m0 st 240 o HAD ltac:(reflexivity) H8 ltac:(lia)) as [_ A2].
    destruct (addressable_split8 m0 (st + o) (240 - o) k A2 ltac:(Z.div_mod_to_equations; lia) K8 ltac:(lia)) as [A3 _].
    exact A3.
  Qed.

  Lemma blk_noX : forall b X, DENV -> In b L9 -> Forall (fun iv : Z * Z => st <= fst iv /\ snd iv <= st + 240) X ->
    Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) X.
  Proof.
    intros b X DE Hb FX. denv DE. pose proof (BAP b Hb) as D. clear - D FX.
    eapply Forall_impl; [|exact FX]. intros [l h] [K1 K2]. cbn [fst snd] in *. lia.
  Qed.
  Lemma blksh_noX : forall s LBc m b X, DENV -> as_RHEAP H s LBc m -> In b LBc ->
    Forall (fun iv : Z * Z => st <= fst iv /\ snd iv <= st + 240) X ->
    forall a, sh (blk_addr b) <= a < sh (blk_addr b) + nsh (blk_size b) -> ~ rin_ivs X a.
  Proof.
    intros s LBc m b X DE RH Hb FX a Ha. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof (ah_blocks H HH _ _ _ b RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    clear - FX Ha B4 R0 Rn RC AC1 AC2.
    assert (S1 : sh (blk_addr b) + nsh (blk_size b) <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
    assert (S2 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; pose proof (Z.div_pos (blk_addr b) 8); lia).
    clear - FX Ha S1 S2 B4. induction X as [|[l h] X IH]; [cbn; tauto|]. cbn [rin_ivs fst snd].
    pose proof (Forall_inv FX) as K1. cbn [fst snd] in K1. pose proof (Forall_inv_tail FX) as K2.
    unfold ASHADOW_BASE, AHI_LO in *. intros [K|K]; [lia | exact (IH K2 K)].
  Qed.
  Lemma in_LBc : forall LBc L b, Permutation LBc (LB0 ++ L) -> In b L -> In b LBc.
  Proof. intros LBc L b P Hb. apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. right. exact Hb. Qed.
  Lemma lb0_LBc : forall LBc L b, Permutation LBc (LB0 ++ L) -> In b LB0 -> In b LBc.
  Proof. intros LBc L b P Hb. apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. left. exact Hb. Qed.

  Lemma rfs_apres : forall LBk SP m m', DENV -> as_RFS H LF m -> apres H LBk SP m m' -> as_RFS H LF m'.
  Proof.
    intros LBk SP m m' DE RF AP. denv DE.
    eapply (ah_RFS_ext H HH); [exact RF|]. intros a Ha Hr. apply (AP a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
    - right; right; right; right; left; exact Hr.
    - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
    - right; right; right; right; right; left; exact Hr.
  Qed.
  Lemma stack0_apres : forall LBk SP m m', DENV -> stack0 m lo shi -> apres H LBk SP m m' -> stack0 m' lo shi.
  Proof. intros LBk SP m m' DE S0 AP. eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP) | exact S0 | apply Forall_nil]. Qed.

  Lemma hdr_at : forall s LBc m X L o cs, DENV -> INV s LBc m X L -> rw_cells asegs m0 (st + o) cs ->
    0 <= o -> o + Z.of_nat (cells_size cs) <= 240 ->
    Forall (fun iv : Z * Z => st + o + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= st + o) X ->
    rw_cells asegs m (st + o) cs.
  Proof.
    intros s LBc m X L o cs DE INV0 C Ho Hn FXh. destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & _).
    eapply (xpres_rw_cells H); [exact XP | exact C |]. apply (st_xcr LBc spz X o _ DE); [lia | lia | exact Hn | exact FXh].
  Qed.
  Lemma hsh_at : forall s LBc m X L o k, DENV -> INV s LBc m X L -> 0 <= o -> o mod 8 = 0 -> 0 <= k -> o + 8 * k <= 240 ->
    SHAD m (st + o) (repeat (b8 0) (Z.to_nat k)).
  Proof.
    intros s LBc m X L o k DE INV0 Ho H8 Hk Hok. pose proof DE as DE0. denv DE.
    destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & FX & _).
    pose proof (st_addr o (8 * k) DE0 Ho H8 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) Hok) as [_ A].
    assert (SO : shadow_of (8 * k) = repeat (b8 0) (Z.to_nat k)).
    { unfold shadow_of. replace (8 * k / 8) with k by (Z.div_mod_to_equations; lia).
      replace ((8 * k) mod 8) with 0 by (Z.div_mod_to_equations; lia). cbn [Z.eqb]. rewrite app_nil_r. reflexivity. }
    rewrite SO in A.
    eapply (SHAD_xp H); [exact XP | exact A |]. intros a Ha. apply (st_sh_xc LBc spz X a DE0); [lia | | exact FX].
    rewrite repeat_length, Z2Nat.id in Ha by lia. clear - Ha STA H8 Hok Ho. unfold sh in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma stage_e : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DM1_B) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X M1b -> Forall (fun iv : Z * Z => st + 64 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & _ & _ & _ & _ & (M1C & M1N & M1L & MN1)).
    destruct INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    pose proof (rw_cells3_split _ _ _ _ _ M1C) as [M1C2 _].
    assert (HC : rw_cells asegs m (st + 48) [C8 (wz mb1); C8 (wz mc1)]).
    { eapply (xpres_rw_cells H); [exact XP | exact M1C2 |].
      replace (Z.of_nat (cells_size [C8 (wz mb1); C8 (wz mc1)])) with 16 by reflexivity.
      apply (st_xcr LBc spz X 48 16 DE0); [lia | lia | lia | eapply Forall_impl; [|exact FXh]; intros [l h] K; cbn [fst snd] in *; lia]. }
    assert (HS : SHAD m (st + 48) (repeat (b8 0) 2)).
    { pose proof (st_addr 48 16 DE0 ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia)) as [_ A].
      change (shadow_of 16) with (repeat (b8 0) 2) in A.
      eapply (SHAD_xp H); [exact XP | exact A |]. intros a Ha. apply (st_sh_xc LBc spz X a DE0); [lia | | exact FX].
      cbn [length repeat Z.of_nat Pos.of_succ_nat] in Ha. clear - Ha STA. unfold sh in *. Z.div_mod_to_equations. lia. }
    assert (BK : mb1 <> 0 -> In (mq1, mb1, 8 * mc1) LBc /\ addressable m mb1 (8 * mc1) /\ st + ST_SIZE <= aceil).
    { intros Hb. destruct M1L as [[E _]|(_ & E & AD)]; [contradiction|].
      assert (INb : In (mq1, mb1, 8 * mc1) LBc) by (eapply in_LBc; [exact PE | rewrite E; left; reflexivity]).
      split; [exact INb|]. split.
      - eapply (addressable_xp H); [exact XP | exact AD |]. intros a Ha. split.
        + right; right; right; left. exists (mq1, mb1, 8 * mc1). split; [exact INb | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia].
        + eapply (blksh_noX s LBc m (mq1, mb1, 8 * mc1) X DE0 RH INb FX). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]. lia.
      - apply STC. unfold L9. rewrite E. cbn. discriminate. }
    assert (HLOC : st_live_frame LF st \/ (spf + 48 <= st /\ st + ST_SIZE + 64 <= shi))
      by (unfold spf; replace (spz - 48 + 48) with spz by lia; exact LOC).
    assert (STb : stk asegs m lo (spf + 48)) by (unfold spf; replace (spz - 48 + 48) with spz by lia; exact ST).
    eapply (dtm1e H HH HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              ra s0 s1 s2 F fc msF m s LBc LF st spf lo B shi errv mo mb1 mc1 mq1);
      [ exact VIS | exact FR | exact HC | exact HS | exact STA | exact HLOC | exact BK | exact OWN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia | exact STb | exact LO1 | unfold spf, AFREE_STACK; lia | exact ERR | exact MI | exact TPV
      | unfold spf; clear - SP16; Z.div_mod_to_equations; lia | unfold spf; lia | unfold spf; lia | exact AC | exact RF | exact S0
      | unfold spf; pose proof SHH; lia | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' AC' RF' S0' RH' OWN' XP' AL' WO'.
    unfold spf in VIS', ST', XP'. replace (spz - 48 + 48) with spz in VIS', ST', XP' by lia.
    assert (ND : List.NoDup (map blk_id LBc)) by exact (ah_nodup H HH _ _ _ RH).
    assert (PF : Permutation (dv_LB H LBc mq1 mb1) LB0).
    { unfold dv_LB. destruct M1L as [(E1 & E2)|(E1 & E2 & _)].
      - rewrite E1, Z.eqb_refl. rewrite E2, app_nil_r in PE. exact PE.
      - rewrite (proj2 (Z.eqb_neq mb1 0) E1). rewrite E2 in PE.
        pose proof (lb_remove_perm_app H HH LBc LB0 [] mq1 mb1 (8 * mc1) ND PE) as K. rewrite app_nil_r in K. exact K. }
    unfold QF, st_dtor_post.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv, s', (dv_LB H LBc mq1 mb1), [], F, fc.
    rewrite u64_of_Z by lia.
    split; [exact VIS'|]. split; [exact FRZ|]. split; [exact KR'|]. split; [eapply (ah_mpres_trans H HH); [exact MP | exact MP']|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact RA'|]. split; [exact RH'|].
    split; [exact PF|]. split; [apply Forall_nil|].
    split.
    { eapply (xpres_trans H).
      - eapply (xpres_weaken H); [exact XP | lia | intros b Hb; exact (lb0_LBc LBc _ b PE Hb) |].
        intros a Ha. cbn [rin_ivs fst snd]. left. clear - Ha FX. induction X as [|[l h] X IH]; [destruct Ha|].
        cbn [rin_ivs fst snd] in Ha. pose proof (Forall_inv FX) as K1. cbn [fst snd] in K1. pose proof (Forall_inv_tail FX) as K2.
        unfold ST_SIZE. destruct Ha as [Ha|Ha]; [lia | exact (IH K2 Ha)].
      - eapply (xpres_weaken H); [exact XP' | lia | intros b Hb; exact (Permutation_in _ (Permutation_sym PF) Hb) |].
        intros a Ha. cbn [rin_ivs fst snd] in *. unfold ST_SIZE. lia. }
    split; [exact RF'|]. split; [exact AC'|]. split; [exact S0'|]. split; [lia|]. split; [exact OWN'|].
    unfold ST_SIZE. exact (st_wr_keep _ spz _ m m' DE0 ltac:(lia) XP' (wr_one m' (st + 48) (st + 56) 8 WO' ltac:(ring)) WST).
  Qed.

  Lemma stage_1h : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DM1) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n) -> Forall (fun iv : Z * Z => st + 72 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & _ & _ & _ & _ & (M1C & M1N & M1L & MN1)).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    pose proof (rw_cells3_split _ _ _ _ _ M1C) as [_ M1C3]. replace (st + 48 + 16) with (st + 64) in M1C3 by lia.
    assert (HC : rw_cells asegs m (st + 64) [C8 (wz (hdq mn1))]).
    { eapply (hdr_at s LBc m X _ 64 _ DE0 INV0 M1C3); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 64 1 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (INn : forall b, In b M1n -> In b LBc) by (intros b Hb; eapply in_LBc; [exact PE | apply in_or_app; right; exact Hb]).
    assert (NO : nodes_okG 24 M1n m mn1).
    { eapply (nodes_okG_xp H 24 M1n mn1 LBc spz X m0 m ltac:(lia) M1N XP INn).
      - intros b Hb. apply (blk_noX b X DE0); [unfold L9; apply in_or_app; right; apply in_or_app; left; exact Hb | exact FX].
      - intros b Hb. exact (blksh_noX s LBc m b X DE0 RH (INn b Hb) FX). }
    assert (PE' : Permutation LBc ((LB0 ++ M1b) ++ M1n)) by (rewrite <- app_assoc; exact PE).
    assert (STN : mn1 <> [] -> st + ST_SIZE <= aceil).
    { intros NE. apply STC. intros E. apply NE. apply MN1. unfold L9 in E.
      destruct M1n; [reflexivity|]. destruct M1b; discriminate E. }
    eapply (dtm1h H HH HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc (LB0 ++ M1b) M1n st spf lo B shi errv mo mn1);
      [ exact VIS | exact HC | exact HS | exact STA | | exact NO | exact PE' | exact STN | exact RH | exact KR | lia | exact RA | unfold spf; lia
      | exact (proj1 (stk_split asegs m lo spf spz ST ltac:(unfold spf; lia))) | exact LO1 | unfold spf, AFREE_STACK; lia | exact ERR | exact MI
      | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia | unfold spf; lia | exact AC | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    { destruct (st_where DE0) as [(W1 & W2 & _)|(W1 & W2)]; [left; eapply aapp_sub; [exact (proj2 (proj2 (proj2 FSBOK))) | lia | unfold ST_SIZE; lia] | right; unfold spf, ST_SIZE; lia]. }
    intros msF' mo' m' s' LBr' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' PL AP' RH' AL'.
    assert (INC : forall b, In b LBr' -> In b LBc).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym PE')). apply in_or_app. left. exact (Permutation_in _ PL Hb). }
    assert (OWN' : lb_own LBr' m').
    { eapply (lb_own_apres H); [| exact AP' | intros b Hb; exact Hb].
      eapply lb_own_incl; [exact INC | exact OWN]. }
    pose proof (INV_step spf s LBc m X (M1b ++ M1n) s' LBr' m' [] M1b DE0 ltac:(lia) INV0 (xpres_of_apres H _ _ _ _ _ AP') INC (Forall_nil _)
                  MI' ST' ERR' RA' AC' (rfs_apres _ _ _ _ DE0 RF AP') (stack0_apres _ _ _ _ DE0 S0 AP') RH' OWN' AL'
                  ltac:(eapply Permutation_trans; [exact PL | apply Permutation_refl]) (Forall_nil _)) as INV1.
    eapply (stage_e s' LBr' m' (X ++ []) msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    rewrite app_nil_r. eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. lia.
  Qed.

  Lemma dvlb_perm : forall LBc L p A n Lx, DENV -> Permutation LBc (LB0 ++ L ++ Lx) -> List.NoDup (map blk_id LBc) ->
    ((A = 0 /\ Lx = []) \/ (A <> 0 /\ Lx = [(p, A, n)])) ->
    Permutation (dv_LB H LBc p A) (LB0 ++ L).
  Proof.
    intros LBc L p A n Lx DE PE ND K. pose proof DE as DE0. denv DE. unfold dv_LB. destruct K as [(E1 & E2)|(E1 & E2)].
    - rewrite E1, Z.eqb_refl. rewrite E2, app_nil_r in PE. exact PE.
    - rewrite (proj2 (Z.eqb_neq A 0) E1). rewrite E2 in PE. rewrite app_assoc in PE.
      pose proof (lb_remove_perm_app H HH LBc (LB0 ++ L) [] p A n ND PE) as K. rewrite app_nil_r in K. exact K.
  Qed.
  Lemma dvlb_incl : forall LBc p A b, DENV -> In b (dv_LB H LBc p A) -> In b LBc.
  Proof.
    intros LBc p A b DE Hb. denv DE. unfold dv_LB in Hb. destruct (A =? 0); [exact Hb|].
    pose proof (ah_lb_remove H HH) as (_ & _ & L3). exact (L3 _ _ _ Hb).
  Qed.
  Lemma loc_spf : DENV -> st_live_frame LF st \/ (spf <= st /\ st + ST_SIZE + 64 <= shi).
  Proof. intros DE. denv DE. destruct LOC as [K|K]; [left; exact K | right; unfold spf; lia]. Qed.
  Lemma loc_spf16 : DENV -> st_live_frame LF st \/ (spf + 16 <= st /\ st + ST_SIZE + 64 <= shi).
  Proof. intros DE. denv DE. destruct LOC as [K|K]; [left; exact K | right; unfold spf; lia]. Qed.
  Lemma aloc_spf : DENV -> aapp st ST_SIZE \/ (spf <= st /\ st + ST_SIZE + 64 <= shi).
  Proof.
    intros DE. pose proof DE as DE0. denv DE.
    destruct (st_where DE0) as [(W1 & W2 & _)|(W1 & W2)];
      [left; eapply aapp_sub; [exact (proj2 (proj2 (proj2 FSBOK))) | lia | unfold ST_SIZE; lia] | right; unfold spf, ST_SIZE; lia].
  Qed.

  Lemma stage_2b : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DM2_B) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n ++ M2b) -> Forall (fun iv : Z * Z => st + 112 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & _ & _ & _ & (M2C & M2N & M2L & MN2) & _).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    pose proof (rw_cells3_split _ _ _ _ _ M2C) as [M2C2 _].
    assert (HC : rw_cells asegs m (st + 88) [C8 (wz mb2); C8 (wz mc2)]).
    { eapply (hdr_at s LBc m X _ 88 _ DE0 INV0 M2C2); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 88 2 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (BK : mb2 <> 0 -> In (mq2, mb2, 8 * mc2) LBc /\ addressable m mb2 (8 * mc2) /\ st + ST_SIZE <= aceil).
    { intros Hb. destruct M2L as [[E _]|(_ & E & AD)]; [contradiction|].
      assert (INb : In (mq2, mb2, 8 * mc2) LBc)
        by (eapply in_LBc; [exact PE | rewrite E; apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
      split; [exact INb|]. split.
      - eapply (addressable_xp H); [exact XP | exact AD |]. intros a Ha. split.
        + right; right; right; left. exists (mq2, mb2, 8 * mc2). split; [exact INb | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia].
        + eapply (blksh_noX s LBc m (mq2, mb2, 8 * mc2) X DE0 RH INb FX). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]. lia.
      - apply STC. unfold L9. rewrite E. intros K. destruct M1b; [destruct M1n; discriminate K | discriminate K]. }
    eapply (dtm2b H HH HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc LF st spf lo B shi errv mo mb2 mc2 mq2);
      [ exact VIS | exact HC | exact HS | exact STA | exact (loc_spf DE0) | exact BK | exact OWN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia | exact (proj1 (stk_split asegs m lo spf spz ST ltac:(unfold spf; lia))) | exact LO1
      | unfold spf, AFREE_STACK; lia | exact ERR | exact MI | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia
      | unfold spf; lia | exact AC | exact RF | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' RF' S0' RH' OWN' XP' AL' WO'.
    assert (ND : List.NoDup (map blk_id LBc)) by exact (ah_nodup H HH _ _ _ RH).
    assert (PL : Permutation (dv_LB H LBc mq2 mb2) (LB0 ++ M1b ++ M1n)).
    { eapply (dvlb_perm LBc (M1b ++ M1n) mq2 mb2 (8 * mc2) M2b DE0); [rewrite <- !app_assoc; exact PE | exact ND |].
      destruct M2L as [K|(K1 & K2 & _)]; [left; exact K | right; exact (conj K1 K2)]. }
    pose proof (INV_step spf s LBc m X (M1b ++ M1n ++ M2b) s' (dv_LB H LBc mq2 mb2) m' [(st + 88, st + 96)] (M1b ++ M1n) DE0 ltac:(lia) INV0 XP'
                  (fun b Hb => dvlb_incl LBc mq2 mb2 b DE0 Hb) ltac:(repeat constructor; cbn; lia)
                  MI' ST' ERR' RA' AC' RF' S0' RH' OWN' AL' PL (wr_one m' (st + 88) (st + 96) 8 WO' ltac:(ring))) as INV1.
    eapply (stage_1h s' _ m' _ msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    apply Forall_app. split; [eapply Forall_impl; [|exact FXh]; intros [l h] K; cbn [fst snd] in *; lia | repeat constructor; cbn; lia].
  Qed.

  Lemma stage_2h : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DM2) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n ++ M2b ++ M2n) -> Forall (fun iv : Z * Z => st + 112 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & _ & _ & _ & (M2C & M2N & M2L & MN2) & _).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    pose proof (rw_cells3_split _ _ _ _ _ M2C) as [_ M2C3]. replace (st + 88 + 16) with (st + 104) in M2C3 by lia.
    assert (HC : rw_cells asegs m (st + 104) [C8 (wz (hdq mn2))]).
    { eapply (hdr_at s LBc m X _ 104 _ DE0 INV0 M2C3); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 104 1 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (INn : forall b, In b M2n -> In b LBc)
      by (intros b Hb; eapply in_LBc; [exact PE | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]).
    assert (NO : nodes_okG 32 M2n m mn2).
    { eapply (nodes_okG_xp H 32 M2n mn2 LBc spz X m0 m ltac:(lia) M2N XP INn).
      - intros b Hb. apply (blk_noX b X DE0); [unfold L9; rewrite !in_app_iff; right; right; right; left; exact Hb | exact FX].
      - intros b Hb. exact (blksh_noX s LBc m b X DE0 RH (INn b Hb) FX). }
    assert (PE' : Permutation LBc ((LB0 ++ M1b ++ M1n ++ M2b) ++ M2n)) by (rewrite <- !app_assoc; exact PE).
    assert (STN : mn2 <> [] -> st + ST_SIZE <= aceil).
    { intros NE. apply STC. intros E. apply NE. apply MN2. unfold L9 in E.
      destruct M2n; [reflexivity|]. destruct M1b; [destruct M1n; [destruct M2b; discriminate E | discriminate E] | discriminate E]. }
    eapply (dtm2h H HH HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc (LB0 ++ M1b ++ M1n ++ M2b) M2n st spf lo B shi errv mo mn2);
      [ exact VIS | exact HC | exact HS | exact STA | exact (aloc_spf DE0) | exact NO | exact PE' | exact STN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia
      | exact (proj1 (stk_split asegs m lo spf spz ST ltac:(unfold spf; lia))) | exact LO1 | unfold spf, AFREE_STACK; lia | exact ERR | exact MI
      | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia | unfold spf; lia | exact AC | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' LBr' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' PL AP' RH' AL'.
    assert (INC : forall b, In b LBr' -> In b LBc).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym PE')). apply in_or_app. left. exact (Permutation_in _ PL Hb). }
    assert (OWN' : lb_own LBr' m').
    { eapply (lb_own_apres H); [| exact AP' | intros b Hb; exact Hb].
      eapply lb_own_incl; [exact INC | exact OWN]. }
    pose proof (INV_step spf s LBc m X (M1b ++ M1n ++ M2b ++ M2n) s' LBr' m' [] (M1b ++ M1n ++ M2b) DE0 ltac:(lia) INV0 (xpres_of_apres H _ _ _ _ _ AP') INC
                  (Forall_nil _) MI' ST' ERR' RA' AC' (rfs_apres _ _ _ _ DE0 RF AP') (stack0_apres _ _ _ _ DE0 S0 AP') RH' OWN' AL' PL (Forall_nil _)) as INV1.
    eapply (stage_2b s' LBr' m' (X ++ []) msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    rewrite app_nil_r. exact FXh.
  Qed.

  Lemma stage_3b : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DM3_B) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n ++ M2b ++ M2n ++ M3b) -> Forall (fun iv : Z * Z => st + 152 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & _ & _ & (M3C & M3N & M3L & MN3) & _ & _).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    pose proof (rw_cells3_split _ _ _ _ _ M3C) as [M2C2 _].
    assert (HC : rw_cells asegs m (st + 128) [C8 (wz mb3); C8 (wz mc3)]).
    { eapply (hdr_at s LBc m X _ 128 _ DE0 INV0 M2C2); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 128 2 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (BK : mb3 <> 0 -> In (mq3, mb3, 8 * mc3) LBc /\ addressable m mb3 (8 * mc3) /\ st + ST_SIZE <= aceil).
    { intros Hb. destruct M3L as [[E _]|(_ & E & AD)]; [contradiction|].
      assert (INb : In (mq3, mb3, 8 * mc3) LBc)
        by (eapply in_LBc; [exact PE | rewrite E; do 4 (apply in_or_app; right); left; reflexivity]).
      split; [exact INb|]. split.
      - eapply (addressable_xp H); [exact XP | exact AD |]. intros a Ha. split.
        + right; right; right; left. exists (mq3, mb3, 8 * mc3). split; [exact INb | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia].
        + eapply (blksh_noX s LBc m (mq3, mb3, 8 * mc3) X DE0 RH INb FX). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]. lia.
      - apply STC. unfold L9. rewrite E. intros K. apply (f_equal (@length block)) in K. rewrite !length_app in K. cbn [length] in K. lia. }
    eapply (dtm3b H HH HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc LF st spf lo B shi errv mo mb3 mc3 mq3);
      [ exact VIS | exact HC | exact HS | exact STA | exact (loc_spf DE0) | exact BK | exact OWN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia | exact (proj1 (stk_split asegs m lo spf spz ST ltac:(unfold spf; lia))) | exact LO1
      | unfold spf, AFREE_STACK; lia | exact ERR | exact MI | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia
      | unfold spf; lia | exact AC | exact RF | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' RF' S0' RH' OWN' XP' AL' WO'.
    assert (ND : List.NoDup (map blk_id LBc)) by exact (ah_nodup H HH _ _ _ RH).
    assert (PL : Permutation (dv_LB H LBc mq3 mb3) (LB0 ++ M1b ++ M1n ++ M2b ++ M2n)).
    { eapply (dvlb_perm LBc (M1b ++ M1n ++ M2b ++ M2n) mq3 mb3 (8 * mc3) M3b DE0); [rewrite <- !app_assoc; exact PE | exact ND |].
      destruct M3L as [K|(K1 & K2 & _)]; [left; exact K | right; exact (conj K1 K2)]. }
    pose proof (INV_step spf s LBc m X (M1b ++ M1n ++ M2b ++ M2n ++ M3b) s' (dv_LB H LBc mq3 mb3) m' [(st + 128, st + 136)] (M1b ++ M1n ++ M2b ++ M2n) DE0 ltac:(lia) INV0 XP'
                  (fun b Hb => dvlb_incl LBc mq3 mb3 b DE0 Hb) ltac:(repeat constructor; cbn; lia)
                  MI' ST' ERR' RA' AC' RF' S0' RH' OWN' AL' PL (wr_one m' (st + 128) (st + 136) 8 WO' ltac:(ring))) as INV1.
    eapply (stage_2h s' _ m' _ msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    apply Forall_app. split; [eapply Forall_impl; [|exact FXh]; intros [l h] K; cbn [fst snd] in *; lia | repeat constructor; cbn; lia].
  Qed.

  Lemma stage_3h : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DM3) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n) -> Forall (fun iv : Z * Z => st + 152 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & _ & _ & (M3C & M3N & M3L & MN3) & _ & _).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    pose proof (rw_cells3_split _ _ _ _ _ M3C) as [_ M2C3]. replace (st + 128 + 16) with (st + 144) in M2C3 by lia.
    assert (HC : rw_cells asegs m (st + 144) [C8 (wz (hdq mn3))]).
    { eapply (hdr_at s LBc m X _ 144 _ DE0 INV0 M2C3); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 144 1 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (INn : forall b, In b M3n -> In b LBc)
      by (intros b Hb; eapply in_LBc; [exact PE | do 5 (apply in_or_app; right); exact Hb]).
    assert (NO : nodes_okG 24 M3n m mn3).
    { eapply (nodes_okG_xp H 24 M3n mn3 LBc spz X m0 m ltac:(lia) M3N XP INn).
      - intros b Hb. apply (blk_noX b X DE0); [unfold L9; rewrite !in_app_iff; do 5 right; left; exact Hb | exact FX].
      - intros b Hb. exact (blksh_noX s LBc m b X DE0 RH (INn b Hb) FX). }
    assert (PE' : Permutation LBc ((LB0 ++ M1b ++ M1n ++ M2b ++ M2n ++ M3b) ++ M3n)) by (rewrite <- !app_assoc; exact PE).
    assert (STN : mn3 <> [] -> st + ST_SIZE <= aceil).
    { intros NE. apply STC. intros E. apply NE. apply MN3. unfold L9 in E.
      destruct M3n as [|b0 M3n']; [reflexivity|]. exfalso. apply (f_equal (@length block)) in E. rewrite !length_app in E. cbn [length] in E. lia. }
    eapply (dtm3h H HH HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc (LB0 ++ M1b ++ M1n ++ M2b ++ M2n ++ M3b) M3n st spf lo B shi errv mo mn3);
      [ exact VIS | exact HC | exact HS | exact STA | exact (aloc_spf DE0) | exact NO | exact PE' | exact STN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia
      | exact (proj1 (stk_split asegs m lo spf spz ST ltac:(unfold spf; lia))) | exact LO1 | unfold spf, AFREE_STACK; lia | exact ERR | exact MI
      | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia | unfold spf; lia | exact AC | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' LBr' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' PL AP' RH' AL'.
    assert (INC : forall b, In b LBr' -> In b LBc).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym PE')). apply in_or_app. left. exact (Permutation_in _ PL Hb). }
    assert (OWN' : lb_own LBr' m').
    { eapply (lb_own_apres H); [| exact AP' | intros b Hb; exact Hb].
      eapply lb_own_incl; [exact INC | exact OWN]. }
    pose proof (INV_step spf s LBc m X (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n) s' LBr' m' [] (M1b ++ M1n ++ M2b ++ M2n ++ M3b) DE0 ltac:(lia) INV0 (xpres_of_apres H _ _ _ _ _ AP') INC
                  (Forall_nil _) MI' ST' ERR' RA' AC' (rfs_apres _ _ _ _ DE0 RF AP') (stack0_apres _ _ _ _ DE0 S0 AP') RH' OWN' AL' PL (Forall_nil _)) as INV1.
    eapply (stage_3b s' LBr' m' (X ++ []) msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    rewrite app_nil_r. exact FXh.
  Qed.

  Lemma stage_v1 : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DV1) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1) -> Forall (fun iv : Z * Z => st + 192 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & _ & (VC & VZ & VL & VO & VS) & _ & _ & _).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    assert (HC : rw_cells asegs m (st + 168) [C8 (wz vb1); C8 (wz ve1); C8 (wz vc1)]).
    { eapply (hdr_at s LBc m X _ 168 _ DE0 INV0 VC); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 168 3 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (BK : vb1 <> 0 -> In (vp1, vb1, vc1 - vb1) LBc /\ vb1 <= ve1 <= vc1 /\ vc1 - vb1 <= 2 ^ 40
                             /\ SHAD m vb1 (cc_gen (vc1 - vb1) (ve1 - vb1)) /\ (vc1 <= st + 168 \/ st + 192 <= vb1) /\ st_live_frame LF st /\ (ve1 - vb1) mod 20 = 0).
    { intros Hb. destruct VL as [[E _]|(_ & E)]; [contradiction|]. destruct (VO Hb) as (O1 & O2 & O3).
      assert (INL : In (vp1, vb1, vc1 - vb1) L9) by (unfold L9; rewrite E; rewrite !in_app_iff; right; right; right; right; right; right; left; left; reflexivity).
      assert (INb : In (vp1, vb1, vc1 - vb1) LBc) by (eapply in_LBc; [exact PE | rewrite E; rewrite !in_app_iff; right; right; right; right; right; right; left; reflexivity]).
      assert (STc : st + ST_SIZE <= aceil) by (apply STC; intros K; rewrite K in INL; destruct INL).
      split; [exact INb|]. split; [exact O1|]. split; [exact O2|]. split.
      - eapply (SHAD_xp H); [exact XP | exact O3 |]. intros a Ha. split.
        + right; right; right; left. exists (vp1, vb1, vc1 - vb1). split; [exact INb | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]].
          unfold cc_gen, poison_bytes in Ha. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length in Ha by lia.
          assert (NM : nsh (ve1 - vb1) <= nsh (vc1 - vb1)) by (unfold nsh; apply Z.div_le_mono; lia). lia.
        + eapply (blksh_noX s LBc m (vp1, vb1, vc1 - vb1) X DE0 RH INb FX). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd].
          unfold cc_gen, poison_bytes in Ha. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length in Ha by lia.
          assert (NM : nsh (ve1 - vb1) <= nsh (vc1 - vb1)) by (unfold nsh; apply Z.div_le_mono; lia). lia.
      - split; [pose proof (BAP _ INL) as D; cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in D; lia|].
        split; [destruct LOC as [K|K]; [exact K | unfold ST_SIZE in *; pose proof aceil_facts as ((AC1 & AC2) & _ & _); lia] | exact (VS Hb)]. }
    eapply (dtv1 H HH HANN HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc LF st spf lo B shi errv mo vp1 vb1 ve1 vc1);
      [ exact VIS | exact HC | exact HS | exact STA | exact VZ | exact (loc_spf16 DE0) | exact BK | exact OWN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia | exact (proj1 (stk_split asegs m lo (spf + 16) spz ST ltac:(unfold spf; lia))) | exact LO1
      | unfold spf, AFREE_STACK; lia | exact ERR | exact MI | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia
      | unfold spf; lia | exact AC | exact RF | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' RF' S0' RH' OWN' XP' AL' WO'.
    assert (ND : List.NoDup (map blk_id LBc)) by exact (ah_nodup H HH _ _ _ RH).
    assert (PL : Permutation (dv_LB H LBc vp1 vb1) (LB0 ++ M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n)).
    { eapply (dvlb_perm LBc (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n) vp1 vb1 (vc1 - vb1) V1 DE0); [rewrite <- !app_assoc; exact PE | exact ND | exact VL]. }
    pose proof (INV_step (spf + 16) s LBc m X _ s' (dv_LB H LBc vp1 vb1) m' [(st + 168, st + 192)] _ DE0 ltac:(lia) INV0 XP'
                  (fun b Hb => dvlb_incl LBc vp1 vb1 b DE0 Hb) ltac:(repeat constructor; cbn; lia)
                  MI' ST' ERR' RA' AC' RF' S0' RH' OWN' AL' PL (wr_one m' (st + 168) (st + 192) 24 WO' ltac:(ring))) as INV1.
    eapply (stage_3h s' _ m' _ msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    apply Forall_app. split; [eapply Forall_impl; [|exact FXh]; intros [l h] K; cbn [fst snd] in *; lia | repeat constructor; cbn; lia].
  Qed.

  Lemma stage_v2 : forall s LBc m X msF mo
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DV2) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1 ++ V2) -> Forall (fun iv : Z * Z => st + 216 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as (_ & (VC & VZ & VL & VO & VS) & _ & _ & _ & _).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    assert (HC : rw_cells asegs m (st + 192) [C8 (wz vb2); C8 (wz ve2); C8 (wz vc2)]).
    { eapply (hdr_at s LBc m X _ 192 _ DE0 INV0 VC); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 192 3 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (BK : vb2 <> 0 -> In (vp2, vb2, vc2 - vb2) LBc /\ vb2 <= ve2 <= vc2 /\ vc2 - vb2 <= 2 ^ 40
                             /\ SHAD m vb2 (cc_gen (vc2 - vb2) (ve2 - vb2)) /\ (vc2 <= st + 192 \/ st + 216 <= vb2) /\ st_live_frame LF st /\ (ve2 - vb2) mod 4 = 0).
    { intros Hb. destruct VL as [[E _]|(_ & E)]; [contradiction|]. destruct (VO Hb) as (O1 & O2 & O3).
      assert (INL : In (vp2, vb2, vc2 - vb2) L9) by (unfold L9; rewrite E; rewrite !in_app_iff; right; right; right; right; right; right; right; left; left; reflexivity).
      assert (INb : In (vp2, vb2, vc2 - vb2) LBc) by (eapply in_LBc; [exact PE | rewrite E; rewrite !in_app_iff; right; right; right; right; right; right; right; left; reflexivity]).
      assert (STc : st + ST_SIZE <= aceil) by (apply STC; intros K; rewrite K in INL; destruct INL).
      split; [exact INb|]. split; [exact O1|]. split; [exact O2|]. split.
      - eapply (SHAD_xp H); [exact XP | exact O3 |]. intros a Ha. split.
        + right; right; right; left. exists (vp2, vb2, vc2 - vb2). split; [exact INb | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]].
          unfold cc_gen, poison_bytes in Ha. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length in Ha by lia.
          assert (NM : nsh (ve2 - vb2) <= nsh (vc2 - vb2)) by (unfold nsh; apply Z.div_le_mono; lia). lia.
        + eapply (blksh_noX s LBc m (vp2, vb2, vc2 - vb2) X DE0 RH INb FX). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd].
          unfold cc_gen, poison_bytes in Ha. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length in Ha by lia.
          assert (NM : nsh (ve2 - vb2) <= nsh (vc2 - vb2)) by (unfold nsh; apply Z.div_le_mono; lia). lia.
      - split; [pose proof (BAP _ INL) as D; cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in D; lia|].
        split; [destruct LOC as [K|K]; [exact K | unfold ST_SIZE in *; pose proof aceil_facts as ((AC1 & AC2) & _ & _); lia] | exact (VS Hb)]. }
    eapply (dtv2 H HH HANN HCF QF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc LF st spf lo B shi errv mo vp2 vb2 ve2 vc2);
      [ exact VIS | exact HC | exact HS | exact STA | exact VZ | exact (loc_spf16 DE0) | exact BK | exact OWN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia | exact (proj1 (stk_split asegs m lo (spf + 16) spz ST ltac:(unfold spf; lia))) | exact LO1
      | unfold spf, AFREE_STACK; lia | exact ERR | exact MI | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia
      | unfold spf; lia | exact AC | exact RF | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' RF' S0' RH' OWN' XP' AL' WO'.
    assert (ND : List.NoDup (map blk_id LBc)) by exact (ah_nodup H HH _ _ _ RH).
    assert (PL : Permutation (dv_LB H LBc vp2 vb2) (LB0 ++ M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1)).
    { eapply (dvlb_perm LBc (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1) vp2 vb2 (vc2 - vb2) V2 DE0); [rewrite <- !app_assoc; exact PE | exact ND | exact VL]. }
    pose proof (INV_step (spf + 16) s LBc m X _ s' (dv_LB H LBc vp2 vb2) m' [(st + 192, st + 216)] _ DE0 ltac:(lia) INV0 XP'
                  (fun b Hb => dvlb_incl LBc vp2 vb2 b DE0 Hb) ltac:(repeat constructor; cbn; lia)
                  MI' ST' ERR' RA' AC' RF' S0' RH' OWN' AL' PL (wr_one m' (st + 192) (st + 216) 24 WO' ltac:(ring))) as INV1.
    eapply (stage_v1 s' _ m' _ msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    apply Forall_app. split; [eapply Forall_impl; [|exact FXh]; intros [l h] K; cbn [fst snd] in *; lia | repeat constructor; cbn; lia].
  Qed.

  Lemma stage_v3 : forall s LBc m X msF mo
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
    DENV -> DCOMP ->
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 st) y11 y12 y13 y14 y15 y16 y17 y18
                             s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 DV3) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    INV s LBc m X (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1 ++ V2 ++ V3) -> Forall (fun iv : Z * Z => st + 240 <= fst iv \/ snd iv <= st + 48) X ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s LBc m X msF mo y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31
      DE DC VIS KR MP INV0 FXh.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    destruct DC as ((VC & VZ & VL & VO & VS) & _ & _ & _ & _ & _).
    pose proof INV0 as (MI & ST & ERR & RA & AC & RF & S0 & RH & OWN & FR & PE & XP & FX & AL & WST).
    assert (HC : rw_cells asegs m (st + 216) [C8 (wz vb3); C8 (wz ve3); C8 (wz vc3)]).
    { eapply (hdr_at s LBc m X _ 216 _ DE0 INV0 VC); [lia | cbn; lia |].
      eapply Forall_impl; [|exact FXh]. intros [l h] K. cbn [fst snd] in *. cbn. lia. }
    pose proof (hsh_at s LBc m X _ 216 3 DE0 INV0 ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as HS. cbn [Z.to_nat Pos.to_nat] in HS.
    assert (BK : vb3 <> 0 -> In (vp3, vb3, vc3 - vb3) LBc /\ vb3 <= ve3 <= vc3 /\ vc3 - vb3 <= 2 ^ 40
                             /\ SHAD m vb3 (cc_gen (vc3 - vb3) (ve3 - vb3)) /\ (vc3 <= st + 216 \/ st + 240 <= vb3) /\ st_live_frame LF st /\ (ve3 - vb3) mod 4 = 0).
    { intros Hb. destruct VL as [[E _]|(_ & E)]; [contradiction|]. destruct (VO Hb) as (O1 & O2 & O3).
      assert (INL : In (vp3, vb3, vc3 - vb3) L9) by (unfold L9; rewrite E; rewrite !in_app_iff; right; right; right; right; right; right; right; right; left; reflexivity).
      assert (INb : In (vp3, vb3, vc3 - vb3) LBc) by (eapply in_LBc; [exact PE | rewrite E; rewrite !in_app_iff; right; right; right; right; right; right; right; right; left; reflexivity]).
      assert (STc : st + ST_SIZE <= aceil) by (apply STC; intros K; rewrite K in INL; destruct INL).
      split; [exact INb|]. split; [exact O1|]. split; [exact O2|]. split.
      - eapply (SHAD_xp H); [exact XP | exact O3 |]. intros a Ha. split.
        + right; right; right; left. exists (vp3, vb3, vc3 - vb3). split; [exact INb | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]].
          unfold cc_gen, poison_bytes in Ha. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length in Ha by lia.
          assert (NM : nsh (ve3 - vb3) <= nsh (vc3 - vb3)) by (unfold nsh; apply Z.div_le_mono; lia). lia.
        + eapply (blksh_noX s LBc m (vp3, vb3, vc3 - vb3) X DE0 RH INb FX). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd].
          unfold cc_gen, poison_bytes in Ha. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length in Ha by lia.
          assert (NM : nsh (ve3 - vb3) <= nsh (vc3 - vb3)) by (unfold nsh; apply Z.div_le_mono; lia). lia.
      - split; [pose proof (BAP _ INL) as D; cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in D; lia|].
        split; [destruct LOC as [K|K]; [exact K | unfold ST_SIZE in *; pose proof aceil_facts as ((AC1 & AC2) & _ & _); lia] | exact (VS Hb)]. }
    eapply (dtv3 H HH HANN HCF QF y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 gp tp
              F fc msF m s LBc LF st spf lo B shi errv mo vp3 vb3 ve3 vc3);
      [ exact VIS | exact HC | exact HS | exact STA | exact VZ | exact (loc_spf16 DE0) | exact BK | exact OWN | exact RH | exact KR | lia
      | exact RA | unfold spf; lia | exact (proj1 (stk_split asegs m lo (spf + 16) spz ST ltac:(unfold spf; lia))) | exact LO1
      | unfold spf, AFREE_STACK; lia | exact ERR | exact MI | exact TPV | unfold spf; clear - SP16; Z.div_mod_to_equations; lia
      | unfold spf; lia | exact AC | exact RF | exact S0 | unfold spf; pose proof SHH; lia
      | intros _; apply (tr_of _ DE0); apply inZ_of_existsb; vm_compute; reflexivity |].
    intros msF' mo' m' s' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31
      VIS' KR' MP' MI' ST' ERR' RA' AC' RF' S0' RH' OWN' XP' AL' WO'.
    assert (ND : List.NoDup (map blk_id LBc)) by exact (ah_nodup H HH _ _ _ RH).
    assert (PL : Permutation (dv_LB H LBc vp3 vb3) (LB0 ++ M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1 ++ V2)).
    { eapply (dvlb_perm LBc (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ V1 ++ V2) vp3 vb3 (vc3 - vb3) V3 DE0); [rewrite <- !app_assoc; exact PE | exact ND | exact VL]. }
    pose proof (INV_step (spf + 16) s LBc m X _ s' (dv_LB H LBc vp3 vb3) m' [(st + 216, st + 240)] _ DE0 ltac:(lia) INV0 XP'
                  (fun b Hb => dvlb_incl LBc vp3 vb3 b DE0 Hb) ltac:(repeat constructor; cbn; lia)
                  MI' ST' ERR' RA' AC' RF' S0' RH' OWN' AL' PL (wr_one m' (st + 216) (st + 240) 24 WO' ltac:(ring))) as INV1.
    eapply (stage_v2 s' _ m' _ msF' mo'); [exact DE0 | exact DC0 | exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP | exact MP'] | exact INV1 |].
    apply Forall_app. split; [eapply Forall_impl; [|exact FXh]; intros [l h] K; cbn [fst snd] in *; lia | repeat constructor; cbn; lia].
  Qed.

  Lemma stage_p : forall (LB : list block) (msF : machine_state) (mo : Model) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    DENV -> DCOMP ->
    as_VIS H sk0 msF = MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                               s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 AST_DTOR) fc None m0 (seg_rom asegs) ->
    as_AKREL H sk0 (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    mem_inv asegs m0 -> stk asegs m0 lo spz -> rw_cells asegs m0 (errno_addr tp) [C4 errv] -> as_rauxv_ok H m0 B ->
    ACONST m0 -> as_RFS H LF m0 -> stack0 m0 lo shi -> as_RHEAP H sk0 LB m0 -> lb_own LB m0 -> Permutation LB (LB0 ++ L9) ->
    wr_at asegs m0 st 240 ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros LB msF mo t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 DE DC VIS KR MP MI ST ERR RA AC RF S0 RH OWN PE WST0.
    pose proof DE as DE0. pose proof DC as DC0. pose proof (st_bounds DE) as (B1 & B2 & B3 & B4). denv DE.
    pose proof SPR as [SPL SPH]. pose proof LOH as [LO1 LO2]. unfold AST_DTOR_STACK, AFREE_STACK in LO2.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ACONST_shbase m0 AC) as [CG CS].
    remember (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                  s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spz]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m0
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWr (SA (EVar 33) (-48)) (ELit 48);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m0 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m0 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R AST_DTOR m0 (seg_rom asegs) HR HK 40%nat [DV3] (SCR [] [] []) 40%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m0 lg) in Hms; set (M1 := mem_denot E m0 lg) in Hms end end.
    assert (MU1 : munch [(spz - 48, spz)] m0 M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m0 M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (WOK : aclient_write_ok H LB (spz - 48, spz) /\ afs_write_ok H LF (spz - 48, spz) /\ aconst_ok (spz - 48, spz)
                  /\ stack0_ok (spz - 48, spz)).
    { pose proof FSBOK as (FB1 & FB2 & FB3 & FB4).
      split; [left; cbn [Datatypes.fst]; lia|].
      split; [left; cbn [Datatypes.fst Datatypes.snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia|].
      split; [apply aconst_ok_high; [pose proof (proj1 (Z.leb_le (sh AIMG_TOP) (2 ^ 45)) ltac:(vm_compute; reflexivity)); lia | right; left; lia]|].
      unfold stack0_ok. cbn [Datatypes.fst Datatypes.snd]. left. unfold AHI_LO. lia. }
    destruct WOK as (W1 & W2 & W3 & W4).
    destruct (client_frame H HH sk0 LB LF B [(spz - 48, spz)] m0 M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. lia. }
    assert (CE : map (fun v => C8 (edenot E v)) [EVar 18; EVar 9; EVar 8; EVar 1]
                 = [C8 s2; C8 s1; C8 s0; C8 ra]) by (unfold E; subst R; reflexivity).
    assert (FR1 : rw_cells asegs M1 (spf + 16) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { rewrite <- CE.
      change M1 with (mem_denot E m0 (c8log (EVar 33) (-32) [EVar 18; EVar 9; EVar 8; EVar 1])).
      apply rw_cells_c8log; [exact Hlf | unfold estart, spf; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia |].
      destruct ST as (STa & STb & STc). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. unfold spf.
      split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (STc (spz - 48 + 16 + i) ltac:(lia))). }
    assert (XP1 : xpres H LB spz [] m0 M1).
    { eapply (xpres_of_munch H sk0 LB spz [] [(spz - 48, spz)] m0 m0 M1 HH RH MU1 WM1).
      apply Forall_cons; [left; cbn [Datatypes.fst Datatypes.snd]; lia | apply Forall_nil]. }
    assert (INV0 : INV sk0 LB M1 [] L9).
    { split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact AC1|].
      split; [exact RF1|]. split; [exact S01|]. split; [exact RH1|]. split; [exact (lb_own_wmono LB m0 M1 OWN WM1)|].
      split; [exact FR1|]. split; [exact PE|]. split; [exact XP1|]. split; [apply Forall_nil|]. split; [lia|]. exact (wr_at_wmono _ _ _ _ WST0 WM1). }
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms HF) HR0 HRe.
    rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
    assert (G2' : getr R' 2 = Z_to_bv 64 spf) by (rewrite G2; unfold spf; rewrite ?w_addm, ?w_add, ?v_addi_Z by lia; try reflexivity; f_equal; lia).
    rewrite G2', G8, G9, G10, G11 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact HF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_v3 sk0 LB M1 [] msF1 mo1); [exact DE0 | exact DC0 | exact VIS1 | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1]
      | exact INV0 | apply Forall_nil].
  Qed.
End StDt.

Lemma nodes_okG_nil_iff : forall NS LBn m ns, nodes_okG NS LBn m ns -> (ns = [] <-> LBn = []).
Proof. intros NS LBn m ns NO. destruct LBn, ns; cbn in NO; try tauto; split; discriminate. Qed.

Lemma hdq_of_map : forall (V : Type) (ns : list (Z * list byte)) (ents : list (Z * (Z * V))),
  map fst ns = map fst ents -> hdq ns = hdaddr ents.
Proof.
  intros V ns ents E. destruct ns as [|[q tl] ns], ents as [|[p [k v]] ents]; cbn [map fst] in E; try discriminate E; [reflexivity|].
  injection E as E1 _. cbn. exact E1.
Qed.

Section Final.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma map_comp : forall (V : Type) (nval : mem -> Z -> V -> Prop) NS s LB m0 o bl bc (ents : list (Z * (Z * V))) (X : list block),
    8 <= NS -> as_RHEAP H s LB m0 -> (forall b, In b X -> In b LB) ->
    umapx MI_A NS nval (lbl LB) m0 o bl bc ents -> umap_sh m0 NS (bl, bc, ents) -> lb_own X m0 ->
    lbl X = umap_blocks NS bl bc ents -> AIMG_TOP <= o ->
    exists mq Mb Mn mn, Permutation X (Mb ++ Mn)
      /\ rw_cells asegs m0 o [C8 (wz bl); C8 (wz bc); C8 (wz (hdq mn))] /\ nodes_okG NS Mn m0 mn
      /\ ((bl = 0 /\ Mb = []) \/ (bl <> 0 /\ Mb = [(mq, bl, 8 * bc)] /\ addressable m0 bl (8 * bc))) /\ (mn = [] <-> Mn = []).
  Proof.
    intros V nval NS s LB m0 o bl bc ents X HNS RH INC U [SHb SHn] OWN EX Ho.
    unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [fst snd] in SHb, SHn.
    unfold umap_blocks in EX.
    destruct (LbB_HMvaT.lbl_perm_split X _ _ ltac:(rewrite EX; apply Permutation_refl)) as (Mb & Mn & P & Eb & En).
    assert (INb : forall b, In b Mb -> In b X) by (intros b Hb; apply (Permutation_in _ (Permutation_sym P)); apply in_or_app; left; exact Hb).
    assert (INn : forall b, In b Mn -> In b X) by (intros b Hb; apply (Permutation_in _ (Permutation_sym P)); apply in_or_app; right; exact Hb).
    assert (NF : forall p k v, In (p, (k, v)) ents -> addressable m0 p NS /\ AIMG_TOP <= p /\ p + NS <= 2 ^ 47).
    { intros p k v Hin. split; [exact (SHn p k v Hin)|]. destruct (u_node U p k v Hin) as (_ & P0 & P1 & _).
      assert (Hl : In (p, NS) (lbl Mn)) by (rewrite En; apply in_map_iff; exists (p, (k, v)); split; [reflexivity | exact Hin]).
      apply lbl_in_inv in Hl. destruct Hl as (q & Hq).
      pose proof (ah_blocks H HH _ _ _ _ RH (INC _ (INn _ Hq))) as (_ & _ & _ & Q3 & _).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Q3. split; [exact Q3 | lia]. }
    destruct (nodes_existG NS V ents Mn m0 HNS En (u_chain U) (lb_own_incl X Mn m0 INn OWN) NF) as (ns & NO & FS).
    pose proof (hdr3_of_umapx NS V nval _ m0 o bl bc ents U Ho) as HD. rewrite <- (hdq_of_map V ns ents FS) in HD.
    destruct (bkt_blk_cases Mb bl bc Eb) as [(B0 & EM)|(B0 & qb & EM)].
    - exists 0, Mb, Mn, ns. split; [exact P|]. split; [exact HD|]. split; [exact NO|].
      split; [left; split; [destruct (u_blive U) as [[_ K]|[K _]]; [exact K | contradiction] | exact EM] | exact (nodes_okG_nil_iff _ _ _ _ NO)].
    - exists qb, Mb, Mn, ns. split; [exact P|]. split; [exact HD|]. split; [exact NO|].
      split; [right; split; [pose proof (u_bl_lo U B0); lia|]; split; [exact EM | exact (SHb B0)] | exact (nodes_okG_nil_iff _ _ _ _ NO)].
  Qed.

  Lemma vec_comp : forall LB m0 o (b e c : Z) (X : list block),
    vraw MI_A (lbl LB) m0 o b e c -> vec_sh m0 (b, e, c) -> lbl X = vec_blocks (b, e, c) -> AIMG_TOP <= o -> o + 24 <= 2 ^ 64 ->
    (b <> 0 -> c - b <= 2 ^ 40) ->
    exists vp, rw_cells asegs m0 o [C8 (wz b); C8 (wz e); C8 (wz c)]
      /\ (b = 0 -> e = 0 /\ c = 0)
      /\ ((b = 0 /\ X = []) \/ (b <> 0 /\ X = [(vp, b, c - b)]))
      /\ (b <> 0 -> b <= e <= c /\ c - b <= 2 ^ 40 /\ SHAD m0 b (cc_gen (c - b) (e - b))).
  Proof.
    intros LB m0 o b e c X V S EX Ho Ho2 VB.
    pose proof (rw_cells_of_vraw _ _ _ _ _ _ V Ho Ho2) as RC.
    pose proof V as [_ _ _ K].
    destruct (vec_blk_cases X (b, e, c) EX) as [(B0 & EX')|(B0 & vp & EX')]; unfold HStmts.t3a, HStmts.t3c in *; cbn [fst snd] in *.
    - exists 0. split; [exact RC|]. split; [intros _; destruct K as [(_ & K1 & K2)|(K0 & _)]; [split; assumption | contradiction]|].
      split; [left; split; assumption | intros Hb; contradiction].
    - exists vp. split; [exact RC|]. split; [intros Hb; contradiction|]. split; [right; split; assumption|].
      intros _. destruct K as [(K0 & _)|(_ & _ & K2)]; [contradiction|]. split; [exact K2|]. split; [exact (VB B0)|].
      unfold vec_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in S. cbn [fst snd] in S. exact (S B0).
  Qed.
End Final.

Theorem st_dtor_ok : forall {HCEIL : HeapCeil} (H : asr), asan_rt_hyps_bp H -> st_dtor_stmt H.
Proof.
  intros HCEIL H HR. pose proof (rt_bp_base H HR) as HH. pose proof (rt_bp_cost H HR) as [HCF _].
  pose proof (rt_bp_annot H HR) as HANN.
  unfold st_dtor_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s
    LB LB0 LBs LF st c lo B shi errv CH
    VIS FRZ Ha0 [REP VSTR] SHc PERM PL VB AD BL LOC SB0 RH KR AL0 RA SPB B64 SP16 ST CE LO ERR MI TPV RAE AC RF S0 SHI OWN TRS
    CHN TRC CHA.
  subst a0.
  set (spz := bv_unsigned sp) in *.
  assert (HSP : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite HSP in VIS |- *.
  pose proof aceil_facts as ((AC1 & AC2) & _ & _).
  pose proof (stack0_bounds _ _ _ S0) as [SB1 SB2]. unfold AAPP_HI in SB2.
  unfold AST_DTOR_STACK, AFREE_STACK in LO.
  pose proof (ah_fsb H HH _ _ _ RH) as FSBOK.
  pose proof (ah_RFS_range H HH LF m RF) as (_ & RR).
  pose proof (sr_al _ _ _ _ _ _ _ REP) as STA.

  assert (STB : AIMG_TOP <= st /\ st + 240 <= 2 ^ 47).
  { destruct LOC as [(f & INF & K1 & K2)|K].
    - destruct (RR f INF) as (Q0 & Q1 & Q2 & _). pose proof FSBOK as (FB1 & FB2 & _). unfold AFS_HDR, AFS_SIZE, ST_SIZE in *. lia.
    - unfold ST_SIZE in K. unfold AIMG_TOP. lia. }

  destruct (split6 LBs c PL) as (X1 & X2 & X3 & X4 & X5 & X6 & PX & LX1 & LX2 & LX3 & LX4 & LX5 & LX6).
  assert (INX : forall b, In b (X1 ++ X2 ++ X3 ++ X4 ++ X5 ++ X6) -> In b LB).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (Permutation_in _ (Permutation_sym PX) Hb). }
  assert (OWNX : forall Xk, (forall b, In b Xk -> In b (X1 ++ X2 ++ X3 ++ X4 ++ X5 ++ X6)) -> lb_own Xk m).
  { intros Xk INk. eapply lb_own_incl; [| exact OWN]. intros b Hb. exact (INX b (INk b Hb)). }
  destruct SHc as (SH1 & SH2 & SH3 & SV1 & SV2 & SV3).
  destruct (st_m1 c) as [[bl1 bc1] e1] eqn:EM1. destruct (st_m2 c) as [[bl2 bc2] e2] eqn:EM2. destruct (st_m3 c) as [[bl3 bc3] e3] eqn:EM3.
  destruct (st_v1 c) as [[b1 en1] c1] eqn:EV1. destruct (st_v2 c) as [[b2 en2] c2] eqn:EV2. destruct (st_v3 c) as [[b3 en3] c3] eqn:EV3.
  pose proof (sr_m1 _ _ _ _ _ _ _ REP) as U1. pose proof (sr_m2 _ _ _ _ _ _ _ REP) as U2. pose proof (sr_m3 _ _ _ _ _ _ _ REP) as U3.
  pose proof (sr_v1 _ _ _ _ _ _ _ REP) as W1. pose proof (sr_v2 _ _ _ _ _ _ _ REP) as W2. pose proof (sr_v3 _ _ _ _ _ _ _ REP) as W3.
  unfold cb_m1, cb_m2, cb_m3, cb_v1, cb_v2, cb_v3 in LX1, LX2, LX3, LX4, LX5, LX6.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in U1.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in U2.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in U3.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in W1.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in W2.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in W3.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in SH1.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in SH2.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in SH3.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in SV1.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in SV2.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in SV3.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in LX1.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in LX2.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in LX3.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in LX4.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in LX5.
  rewrite ?EM1, ?EM2, ?EM3, ?EV1, ?EV2, ?EV3 in LX6.
  cbn [HStmts.t3a HStmts.t3b HStmts.t3c fst snd] in U1, U2, U3, W1, W2, W3, LX1, LX2, LX3, LX4, LX5, LX6.
  unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in U1, U2, U3, W1, W2, W3. cbn [fst snd] in U1, U2, U3, W1, W2, W3.

  assert (VB1 : b1 <> 0 -> c1 - b1 <= 2 ^ 40).
  { intros Hb. apply (VB b1 (c1 - b1)). rewrite state_blocks_cb. unfold cb_v1. rewrite EV1.
    unfold vec_blocks, HStmts.t3a, HStmts.t3c. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq b1 0) Hb).
    rewrite !in_app_iff. right; right; right; left. cbn [In]. left; reflexivity. }
  assert (VB2 : b2 <> 0 -> c2 - b2 <= 2 ^ 40).
  { intros Hb. apply (VB b2 (c2 - b2)). rewrite state_blocks_cb. unfold cb_v2. rewrite EV2.
    unfold vec_blocks, HStmts.t3a, HStmts.t3c. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq b2 0) Hb).
    rewrite !in_app_iff. right; right; right; right; left. cbn [In]. left; reflexivity. }
  assert (VB3 : b3 <> 0 -> c3 - b3 <= 2 ^ 40).
  { intros Hb. apply (VB b3 (c3 - b3)). rewrite state_blocks_cb. unfold cb_v3. rewrite EV3.
    unfold vec_blocks, HStmts.t3a, HStmts.t3c. cbn [fst snd]. rewrite (proj2 (Z.eqb_neq b3 0) Hb).
    rewrite !in_app_iff. right; right; right; right; right. cbn [In]. left; reflexivity. }
  destruct (vec_comp _ m (st + 168) b1 en1 c1 X4 W1 SV1 LX4 ltac:(unfold AIMG_TOP in *; lia) ltac:(lia)
              VB1) as (vp1 & VC1 & VZ1 & VL1 & VO1).
  destruct (vec_comp _ m (st + 192) b2 en2 c2 X5 W2 SV2 LX5 ltac:(unfold AIMG_TOP in *; lia) ltac:(lia)
              VB2) as (vp2 & VC2 & VZ2 & VL2 & VO2).
  destruct (vec_comp _ m (st + 216) b3 en3 c3 X6 W3 SV3 LX6 ltac:(unfold AIMG_TOP in *; lia) ltac:(lia)
              VB3) as (vp3 & VC3 & VZ3 & VL3 & VO3).
  destruct (map_comp H HH Z (nval24 ASEGS) 24 s LB m (st + 48) bl1 bc1 e1 X1 ltac:(lia) RH
              ltac:(intros b Hb; apply INX; apply in_or_app; left; exact Hb) U1 SH1
              (OWNX X1 ltac:(intros b Hb; apply in_or_app; left; exact Hb)) LX1 ltac:(unfold AIMG_TOP in *; lia))
    as (mq1 & M1b & M1n & mn1 & PM1 & MC1 & MN1 & ML1 & MI1).
  destruct (map_comp H HH (Z * Z * Z)%type (nval32 ASEGS) 32 s LB m (st + 88) bl2 bc2 e2 X2 ltac:(lia) RH
              ltac:(intros b Hb; apply INX; apply in_or_app; right; apply in_or_app; left; exact Hb) U2 SH2
              (OWNX X2 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) LX2 ltac:(unfold AIMG_TOP in *; lia))
    as (mq2 & M2b & M2n & mn2 & PM2 & MC2 & MN2 & ML2 & MI2).
  destruct (map_comp H HH Z (nval24 ASEGS) 24 s LB m (st + 128) bl3 bc3 e3 X3 ltac:(lia) RH
              ltac:(intros b Hb; apply INX; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb) U3 SH3
              (OWNX X3 ltac:(intros b Hb; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) LX3 ltac:(unfold AIMG_TOP in *; lia))
    as (mq3 & M3b & M3n & mn3 & PM3 & MC3 & MN3 & ML3 & MI3).

  assert (PL9 : Permutation LB (LB0 ++ (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ X4 ++ X5 ++ X6))).
  { eapply Permutation_trans; [exact PERM|]. apply Permutation_app_head.
    eapply Permutation_trans; [exact PX|]. rewrite (app_assoc M1b M1n).
    apply Permutation_app; [exact PM1|]. rewrite (app_assoc M2b M2n).
    apply Permutation_app; [exact PM2|]. rewrite (app_assoc M3b M3n).
    apply Permutation_app; [exact PM3|]. apply Permutation_refl. }
  assert (IN9 : forall b, In b (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ X4 ++ X5 ++ X6) -> In b LB).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym PL9)). apply in_or_app. right. exact Hb. }
  eapply (stage_p H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc spz st LB0 LF lo B shi errv m mo s
            b3 en3 c3 b2 en2 c2 b1 en1 c1 vp3 vp2 vp1 X6 X5 X4 bl3 bc3 bl2 bc2 bl1 bc1 mq3 mq2 mq1 M3b M3n M2b M2n M1b M1n mn3 mn2 mn1
            LB msF mo t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6);
    [ | | exact VIS | exact KR | apply (ah_mpres_refl H HH) | exact MI | exact ST | exact ERR | exact RA | exact AC | exact RF | exact S0
      | exact RH | exact OWN | exact PL9
      | apply wr_at_of_defined; [exact (sr_def _ _ _ _ _ _ _ REP) | unfold AIMG_TOP in *; lia | lia] ].
  -
    split; [exact HH|]. split; [exact HANN|]. split; [exact HCF|]. split; [exact FRZ|]. split; [exact SP16|].
    split; [split; [clear - AC1 CE LO; lia | clear - SHI SB2; lia]|].
    split; [unfold AST_DTOR_STACK, AFREE_STACK; split; [exact CE | clear - LO; lia]|].
    split; [split; [exact SHI | unfold AAPP_HI; clear - SB2; lia]|].
    split; [exact SPB|]. split; [exact TPV|]. split; [exact RAE|]. split; [exact TRS|]. split; [exact AL0|]. split; [exact LOC|].
    split; [exact STA|]. split; [exact AD|]. split; [exact FSBOK|].
    split; [intros f INF; destruct (RR f INF) as (Q0 & Q1 & Q2 & _); split; [clear - Q0; lia|]; split; [exact Q1 | exact Q2]|].
    split.
    + intros NE. destruct SB0 as [E|E]; [|exact E]. exfalso. apply NE.
      assert (LN : lbl (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ X4 ++ X5 ++ X6) = []).
      { apply Permutation_nil. rewrite <- E. eapply Permutation_trans; [exact (Permutation_sym PL)|].
        unfold lbl. apply Permutation_map.
        eapply Permutation_trans; [exact PX|]. rewrite (app_assoc M1b M1n).
        apply Permutation_app; [exact PM1|]. rewrite (app_assoc M2b M2n).
        apply Permutation_app; [exact PM2|]. rewrite (app_assoc M3b M3n).
        apply Permutation_app; [exact PM3|]. apply Permutation_refl. }
      unfold L9. destruct (M1b ++ M1n ++ M2b ++ M2n ++ M3b ++ M3n ++ X4 ++ X5 ++ X6); [reflexivity | discriminate LN].
    + intros b Hb. pose proof (BL b (IN9 b Hb)) as D. unfold ST_SIZE in D. clear - D. lia.
  -
    destruct VSTR as (VS1 & VS2 & VS3). rewrite ?EV1 in VS1. rewrite ?EV2 in VS2. rewrite ?EV3 in VS3.
    unfold HStmts.t3a, HStmts.t3b in VS1, VS2, VS3. cbn [fst snd] in VS1, VS2, VS3.
    split; [split; [exact VC3 | split; [exact VZ3 | split; [exact VL3 | split; [exact VO3 | exact VS3]]]]|].
    split; [split; [exact VC2 | split; [exact VZ2 | split; [exact VL2 | split; [exact VO2 | exact VS2]]]]|].
    split; [split; [exact VC1 | split; [exact VZ1 | split; [exact VL1 | split; [exact VO1 | exact VS1]]]]|].
    split; [split; [exact MC3 | split; [exact MN3 | split; [exact ML3 | exact MI3]]]|].
    split; [split; [exact MC2 | split; [exact MN2 | split; [exact ML2 | exact MI2]]]|].
    split; [exact MC1 | split; [exact MN1 | split; [exact ML1 | exact MI1]]].
Qed.
