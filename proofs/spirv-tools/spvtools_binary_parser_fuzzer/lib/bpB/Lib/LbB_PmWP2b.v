(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmGlue LbB_PmVops LbB_ContVot LbB_PmWKit LbB_RtOwn LbB_PmDS LbB_WoGen LbB_ContStmt LbB_ContV4 LbB_BiW32S LbB_PmWG.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import ContStmts.












Section VP2b.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Let HHp : asan_rt_hyps H := rt_bp_base H HHbp.

  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.

  Lemma pmxa_vgrow2b : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' (pid pid' : bptr) (b' x : Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    Zlen (t3b (c_v2 c)) = t3c (c_v2 c) ->
    (t3a (c_v2 c) <> 0 -> In (pid, t3a (c_v2 c), 4 * t3c (c_v2 c)) LBs) ->
    pm_bud (wa_n w) (set_v2A c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ->

    as_RHEAP H s' (v4_newLB H LB (t3a (c_v2 c)) pid pid' b' (4 * vgrow (t3c (c_v2 c)))) m' -> as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) ->
    as_rauxv_ok H m' (wa_B w) ->
    xpres H LB (wa_s1 w) ((wa_p w + O_V2, wa_p w + O_V2 + 24) :: v4_oldx (t3a (c_v2 c)) (4 * t3c (c_v2 c))) m m' ->
    ablock_range H b' (4 * vgrow (t3c (c_v2 c))) ->
    vec32A (v4_newLB H LB (t3a (c_v2 c)) pid pid' b' (4 * vgrow (t3c (c_v2 c)))) m' (wa_p w + O_V2) b' (t3b (c_v2 c) ++ [x]) (vgrow (t3c (c_v2 c))) ->
    SHAD m' b' (cc_gen (4 * vgrow (t3c (c_v2 c))) (4 * (t3c (c_v2 c) + 1))) ->
    wr_at asegs m' (wa_p w + O_V2) 24 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s - (as_Cm H (4 * vgrow (t3c (c_v2 c))) + as_Cf H (4 * t3c (c_v2 c))) ->
    PMXAT H LINV w s' (v4_newLB H LB (t3a (c_v2 c)) pid pid' b' (4 * vgrow (t3c (c_v2 c))))
          ((pid', b', 4 * vgrow (t3c (c_v2 c))) :: (if t3a (c_v2 c) =? 0 then LBs else as_lb_remove H pid LBs)) m' mo'
          (set_v2A c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' pid pid' b' x OK X0 Hknn Hfk FULL PIDin BUDc
           RH' MP' MI' STK' ERR' RA' XP ABR' V2' SH' WR' RFS' AC' S0' AL'.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as V2.
    destruct (c_v2 c) as [[b xs] cap] eqn:EV2. cbn [t3a t3b t3c fst snd] in *.
    pose proof V2 as (Hv & Hv' & HD & Hlen & Hb & _).
    assert (Hcap0 : 0 <= cap) by (unfold Zlen in *; lia).
    assert (B0C : b = 0 -> cap = 0) by (intros B0; destruct Hb as [[_ C0]|(Bp & _)]; lia).
    set (cap' := vgrow cap) in *. set (n' := 4 * cap') in *.
    set (LB' := v4_newLB H LB b pid pid' b' n') in *.
    set (c' := set_v2A c (b', xs ++ [x], cap')) in *.
    destruct (rt_bp_cost H HHbp) as [CFz CMz]. rewrite CFz, CMz, Z.add_0_r in AL'.

    destruct (pmxa_keep_but_xp H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal m' (lbl LB') (vx H w O_V2 b (4 * cap)) [] O_V2 (b, 4 * cap)
                OK X0 RFS' ltac:(apply Forall_nil) ltac:(rewrite app_nil_r; exact XP) (vx_vwin H w O_V2 b (4 * cap) ltac:(lia)) ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia)
                ltac:(right; left; split; [reflexivity | unfold blkV2; rewrite EV2; reflexivity]))
      as (U1 & U2 & U3 & S1 & S2 & S3 & K1 & _ & K3).
    { intros q Hq Hne Hl. eapply (vgrow_live H HHbp w s LB LBs TB m c pid pid' b (4 * cap) b' n' (b, 4 * cap) q OK RH OWN1 OWN2 eq_refl PIDin Hq Hne Hl). }
    destruct (K1 ltac:(unfold O_V1, O_V2; lia)) as [V1 S4]. destruct (K3 ltac:(unfold O_V2, O_V3; lia)) as [V3 S6].

    pose proof ABR' as (B'0 & _).
    pose proof (phi_grow_v2 c b' (xs ++ [x]) cap ltac:(rewrite EV2; reflexivity) Hcap0 ltac:(rewrite EV2; cbn [t3a fst snd]; exact B0C) ltac:(lia)) as PG.
    fold cap' in PG. change (set_v2A c (b', xs ++ [x], cap')) with c' in PG. fold n' in PG.
    eapply (pmxa_vgrow_gen H HHbp LINV LINV_cl HOWN w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' c' O_V2 pid pid' b (4 * cap) b' n' (ICM n')
              _ _ [] OK X0 Hknn Hfk ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia));
      [ rewrite (cblocks_v2 c), EV2; cbn [t3a t3c fst snd]; reflexivity
      | unfold c'; rewrite cblocks_set_v2; replace (b' =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity
      | exact PIDin | lia | exact BUDc | exact PG
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact RH' | exact MP' | exact MI' | exact STK' | exact ERR' | exact RA' | apply Forall_nil | rewrite app_nil_r; exact XP | exact ABR' | exact WR' | exact RFS' | exact AC' | exact S0' | exact AL'
      | exact U1 | exact U2 | exact U3 | exact V1 | exact V2' | exact V3 | ].
    subst c'. unfold set_v2A, pmc_sh. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v2]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
    split; [exact S4|]. split; [| exact S6].
    unfold vsh32. cbn [t3a t3b t3c fst snd]. intros _.
    replace (4 * Zlen (xs ++ [x])) with (4 * (cap + 1)) by (unfold Zlen in *; rewrite length_app; cbn [length]; lia). exact SH'.
  Qed.

  Lemma pmxa_vsame2b : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' (pid : bptr) (x : Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    t3a (c_v2 c) <> 0 -> In (pid, t3a (c_v2 c), 4 * t3c (c_v2 c)) LBs ->
    as_RHEAP H s' LB m' -> as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) ->
    as_rauxv_ok H m' (wa_B w) ->
    xpres H LB (wa_s1 w) [(wa_p w + O_V2, wa_p w + O_V2 + 24); (t3a (c_v2 c), t3a (c_v2 c) + 4 * t3c (c_v2 c));
                          (sh (t3a (c_v2 c)), sh (t3a (c_v2 c)) + nsh (4 * t3c (c_v2 c)))] m m' ->
    vec32A LB m' (wa_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c) ++ [x]) (t3c (c_v2 c)) ->
    SHAD m' (t3a (c_v2 c)) (cc_gen (4 * t3c (c_v2 c)) (4 * (Zlen (t3b (c_v2 c)) + 1))) ->
    wr_at asegs m' (wa_p w + O_V2) 24 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s ->
    PMXAT H LINV w s' LB LBs m' mo' (set_v2A c (t3a (c_v2 c), t3b (c_v2 c) ++ [x], t3c (c_v2 c))) ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' pid x OK X0 Hknn Hfk NZ PIDin
           RH' MP' MI' STK' ERR' RA' XP V2' SH' WR' RFS' AC' S0' AL'.
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as V2.
    destruct (c_v2 c) as [[b xs] cap] eqn:EV2. cbn [t3a t3b t3c fst snd] in *.
    pose proof V2 as (Hv & Hv' & HD & Hlen & Hb & _).
    assert (Hcap0 : 0 <= cap) by (unfold Zlen in *; lia).
    set (c' := set_v2A c (b, xs ++ [x], cap)) in *.
    assert (XE : vx H w O_V2 b (4 * cap) = [(wa_p w + O_V2, wa_p w + O_V2 + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))]).
    { unfold vx, v4_oldx. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity. }
    rewrite <- XE in XP.
    destruct (pmxa_keep_but_xp H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal m' (lbl LB) (vx H w O_V2 b (4 * cap)) [] O_V2 (b, 4 * cap)
                OK X0 RFS' ltac:(apply Forall_nil) ltac:(rewrite app_nil_r; exact XP) (vx_vwin H w O_V2 b (4 * cap) ltac:(lia)) ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia)
                ltac:(right; left; split; [reflexivity | unfold blkV2; rewrite EV2; reflexivity]) ltac:(intros q _ _ Hl; exact Hl))
      as (U1 & U2 & U3 & S1 & S2 & S3 & K1 & _ & K3).
    destruct (K1 ltac:(unfold O_V1, O_V2; lia)) as [V1 S4]. destruct (K3 ltac:(unfold O_V2, O_V3; lia)) as [V3 S6].
    eapply (pmxa_vsame_gen H HHbp LINV LINV_cl HOWN w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' c' O_V2 pid b (4 * cap) []
              OK X0 Hknn Hfk ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia));
      [ unfold c'; rewrite cblocks_set_v2, (cblocks_v2 c), EV2; cbn [t3a t3c fst snd]; reflexivity
      | intros _; exact PIDin | lia
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact RH' | exact MP' | exact MI' | exact STK' | exact ERR' | exact RA' | apply Forall_nil | rewrite app_nil_r; exact XP | exact WR' | exact RFS' | exact AC' | exact S0' | exact AL'
      | exact U1 | exact U2 | exact U3 | exact V1 | exact V2' | exact V3 | ].
    subst c'. unfold set_v2A, pmc_sh. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v2]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
    split; [exact S4|]. split; [| exact S6].
    unfold vsh32. cbn [t3a t3b t3c fst snd]. intros _.
    replace (4 * Zlen (xs ++ [x])) with (4 * (Zlen xs + 1)) by (unfold Zlen; rewrite length_app; cbn [length]; lia). exact SH'.
  Qed.

  Lemma pm_vpush2b : biw32_stmt H ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret x : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 BIW32_ENTRY) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + 64) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + 96) ->
    obj_sh_ok ins 64 8 = true -> obj_sh_ok ins 96 4 = true ->
    rw_cells asegs m (wa_ff w + 64) [C8 (Z_to_bv 64 (wa_p w + 240))] ->
    rw_cells asegs m (wa_ff w + 96) [C4 (Z_to_bv 64 x)] -> 0 <= x < 2 ^ 32 ->
    pm_bud (wa_n w) c ->
    (Zlen (t3b (c_v2 c)) = t3c (c_v2 c) -> forall b'' xs'', pm_bud (wa_n w) (set_v2A c (b'', xs'', vgrow (t3c (c_v2 c))))) ->
    (forall msF1 mo1 m1 R1 (s1 : as_St H) (LB1 LBs1 : list block) (b' cap' : Z),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_v2A c (b', t3b (c_v2 c) ++ [x], cap')) ins tbl ftbl TB spal ->
       (forall r, In r V4_KEPT -> PropExec.getr R1 r = PropExec.getr R r) ->
       pm_bud (wa_n w) (set_v2A c (b', t3b (c_v2 c) ++ [x], cap')) ->
       ((Zlen (t3b (c_v2 c)) < t3c (c_v2 c) /\ b' = t3a (c_v2 c) /\ cap' = t3c (c_v2 c) /\ LB1 = LB /\ LBs1 = LBs)
        \/ (Zlen (t3b (c_v2 c)) = t3c (c_v2 c) /\ cap' = vgrow (t3c (c_v2 c)) /\ ablock_range H b' (4 * cap'))) ->
       ffkeep w m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros V4 w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret x Q OK X Hknn Hfk KR VIS RF
           G1 Hr2 Hr G2 G4 G10 G11 Hok64 Hok96 RWI RW Hx BUD BUD' K.
    change (wa_p w + 240) with (wa_p w + O_V2) in RWI.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V2.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & ADp & _).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    pose proof (pmw_frame_facts H w OK) as (E1 & E2 & E3 & _).
    pose proof (xp_geom H HHp w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    assert (TRd : trace_ok (as_TR H) APC0_FREE [v4_del_ra V32_SLOW_RREF]).
    { pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok in TR. rewrite Forall_forall in TR. apply TR.
      unfold PM_DEL_RAS, V32_SLOW_RREF. cbn [v4_del_ra In]. repeat (first [left; reflexivity | right]). }
    destruct (c_v2 c) as [[b xs] cap] eqn:EV2. cbn [t3a t3b t3c fst snd] in *.
    pose proof V2 as (Hv & Hv' & HD & Hlen & Hb & _).
    assert (Hcap0 : 0 <= cap) by (unfold Zlen in *; lia).
    assert (B0C : b = 0 -> cap = 0) by (intros B0; destruct Hb as [[_ C0]|(Bp & _)]; lia).
    set (cap' := vgrow cap) in *.
    assert (VG : cap' >= 2 * cap /\ cap' >= cap + 1) by (unfold cap', vgrow; lia).

    assert (OLD : exists pid, v4_oldblk LB b cap pid /\ (b <> 0 -> In (pid, b, 4 * cap) LBs)).
    { destruct (Z.eq_dec b 0) as [E|E].
      - exists 0. split; [left; split; [exact E | exact (B0C E)] | intros NZ; contradiction].
      - destruct (cblk_facts H HHp LINV w s LB LBs m mo c ins tbl ftbl TB spal b (4 * cap) OK X) as (pid & I1 & I2 & _).
        { rewrite (cblocks_v2 c), EV2. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; left.
          destruct (Z.eqb_spec b 0); [contradiction | left; reflexivity]. }
        exists pid. split; [right; split; [destruct Hb as [[B0 _]|(Bp & _ & Cp & _)]; [contradiction | exact Cp] | exact I2] | intros _; exact I1]. }
    destruct OLD as (pid & OB & PIDin).
    assert (INbLB : b <> 0 -> In (pid, b, 4 * cap) LB).
    { intros E. apply (Permutation_in _ (Permutation_sym OWN1)). apply in_or_app; right. apply in_or_app; left. exact (PIDin E). }

    assert (CAPB : 4 * cap <= 2 ^ 26).
    { pose proof BUD as (_ & _ & _ & _ & _ & Bv2 & _). rewrite EV2 in Bv2. cbn [t3c snd] in Bv2. lia. }
    destruct (rt_bp_cost H HHbp) as [CFz CMz].
    assert (FULLf : Zlen xs = cap -> 4 * cap' <= 2 ^ 26 /\ ICM (4 * cap') <= as_AL H s).
    { intros XSL. set (c'0 := set_v2A c (1, [], cap')).
      assert (BUD0 : pm_bud (wa_n w) c'0) by (unfold c'0; apply (BUD' XSL)).
      pose proof (pm_resv_of_bud (wa_n w) c'0 WN BUD0) as RESV0.
      pose proof (phi_grow_v2 c 1 [] cap ltac:(rewrite EV2; reflexivity) Hcap0 ltac:(rewrite EV2; cbn [t3a fst snd]; exact B0C) ltac:(lia)) as PG. fold cap' c'0 in PG.
      pose proof (pm_phi_le_cap c'0) as PC0.
      pose proof BUD0 as (_ & _ & _ & _ & _ & Bv2 & _). unfold c'0, set_v2A in Bv2. cbn [c_v2 t3c snd] in Bv2. lia. }
    pose proof (pmxa_meas_LB H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X) as (M1 & M2 & M3).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HHp).
    { eapply V4 with (it := wa_ff w + 64) (v := wa_p w + O_V2) (b := b) (cap := cap) (src := wa_ff w + 96) (x := x) (xs := xs) (pid := pid)
        (LB := LB) (LF := PMLF H w) (lo := wa_lo w) (B := wa_B w) (shi := wa_shi w) (errv := errv) (s := s) (m := m) (mo := mo);
      [ exact VIS | exact G10 | exact G11
      | apply fld_of_rw_cells8; [exact RWI | lia]
      | Z.div_mod_to_equations; lia
      | exact (ff_addressable m (wa_ff w) ins 64 8 (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) Hok64)
      | apply (aapp_sub (wa_ff w) 16384); [exact FA | lia | lia]
      | unfold vec32A; exact V2 | unfold O_V2; Z.div_mod_to_equations; lia
      | apply (pw_addr_sub8 m (wa_p w) PARSER_SIZE O_V2 24 ADp); unfold O_V2, PARSER_SIZE; try reflexivity; lia
      | rewrite G2, u64_of_Z by lia; apply (pwin_obj H HHp w LB O_V2 OK); unfold O_V2, PARSER_SIZE; try reflexivity; lia
      | exact (proj1 (pwin_band H w (wa_p w + O_V2) 24 OK ltac:(unfold O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia) ltac:(lia)))
      | apply (wr_at_of_mdef m (wa_p w) PARSER_SIZE O_V2 24 (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); unfold O_V2, PARSER_SIZE; lia
      | exact (HOWN s LB m RH)
      | exact OB
      | intros Cp; pose proof SHc as (_ & _ & _ & _ & SH6 & _); rewrite EV2 in SH6; unfold vsh32 in SH6; cbn [t3a t3b t3c fst snd] in SH6; apply SH6; lia
      | exact CAPB
      | intros XSL; unfold v4_newcap; fold cap'; exact (proj1 (FULLf XSL))
      | rewrite G2, u64_of_Z by lia; apply (ff_src4_keep_x H HHp LINV w s LB LBs m mo c ins tbl ftbl TB spal 96 x _ OK X Hok96 ltac:(lia) ltac:(lia) RW Hx);
          destruct (Z.eqb_spec b 0) as [E|E]; [apply Forall_nil | apply Forall_cons; [exists pid, b, (4 * cap); split; [exact (INbLB E) | cbn [fst snd]; split; reflexivity] | apply Forall_nil]]
      | exact Hx | Z.div_mod_to_equations; lia | lia | lia
      | exact RH | exact KR
      | intros XSL; split;
          [ apply (rt_bp_live H HHbp s LB m (4 * v4_newcap cap) RH); unfold v4_newcap; fold cap';
              [lia | unfold nsmall; destruct (Z.leb_spec (4 * cap') 64512); lia | lia | unfold nlg; destruct (Z.ltb_spec 64512 (4 * cap')); lia]
          | rewrite CFz, CMz; unfold v4_newcap; fold cap'; pose proof (proj2 (FULLf XSL)); lia ]
      | exact TRd
      | exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G2, u64_of_Z by lia; lia
      | rewrite G2, u64_of_Z by lia; Z.div_mod_to_equations; lia | rewrite G2, u64_of_Z by lia; lia
      | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)))
      | lia | rewrite G2, u64_of_Z by lia; unfold BIW32_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK in *; lia
      | rewrite G4; exact ERR | exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G4; exact (wk_tp H w OK)
      | rewrite G1, u64_of_Z by lia; exact Hr2
      | exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | rewrite G2, u64_of_Z by lia; lia ]. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB' & b' & capn & POST).
    cbv zeta in POST.
    destruct POST as (VIS1 & KR1 & MP1 & MI1 & ST1 & ER1 & RA1 & VEC1 & RH1 & SH1 & AD1 & WV1 & OW1 & CASES & RF1 & AC1' & S01).
    cbn [cfg_ms cfg_model] in VIS1, KR1, MP1.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in ST1 by lia. rewrite G4 in ER1.
    destruct CASES as [(XLT & -> & -> & -> & XP1 & AL1) | (XSL & ECAP & (pid' & -> & ABR1) & XP1 & AL1)].
    -
      rewrite G2, u64_of_Z in XP1 by lia.
      assert (NZ : b <> 0) by (intros E; pose proof (B0C E); lia).
      assert (X1 : PMXAT H LINV w s1 LB LBs m1 mo1 (set_v2A c (b, xs ++ [x], cap)) ins tbl ftbl TB spal).
      { pose proof (pmxa_vsame2b w s LB LBs m mo c ins tbl ftbl TB spal s1 m1 mo1 pid x OK X Hknn Hfk) as VSR.
        rewrite EV2 in VSR. cbn [t3a t3b t3c fst snd] in VSR.
        apply VSR; [exact NZ | exact (PIDin NZ) | exact RH1 | exact MP1 | exact MI1 | exact ST1 | exists errv1; exact ER1 | exact RA1
                | exact XP1 | exact VEC1 | exact SH1 | exact WV1 | exact RF1 | exact AC1' | exact S01 | exact AL1]. }
      assert (BUD1 : pm_bud (wa_n w) (set_v2A c (b, xs ++ [x], cap))).
      { unfold pm_bud, set_v2A in *. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v2 c_tr t3a t3b t3c fst snd] in *. rewrite EV2 in BUD. cbn [t3c snd] in BUD. exact BUD. }
      eapply (K ms1 mo1 m1 _ s1 LB LBs b cap); [exact KR1 | exact VIS1 | apply rfull_mkR | exact X1 | | exact BUD1 | left; repeat split; try reflexivity; exact XLT |].
      + intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
      + intros k cs Hk Hkc RWk.
        assert (XE : vx H w O_V2 b (4 * cap) = [(wa_p w + O_V2, wa_p w + O_V2 + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))]).
        { unfold vx, v4_oldx. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity. }
        rewrite <- XE in XP1.
        exact (vx_ff_keep H HHbp w s LB m m1 O_V2 b (4 * cap) pid [] k cs OK RH RF1 ltac:(apply Forall_nil) ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia) INbLB ltac:(lia) ltac:(rewrite app_nil_r; exact XP1) Hk Hkc RWk).
    -
      rewrite G2, u64_of_Z in XP1 by lia.
      unfold v4_newcap in *. fold cap' in ECAP. subst capn.
      assert (X1 : PMXAT H LINV w s1 (v4_newLB H LB b pid pid' b' (4 * cap')) ((pid', b', 4 * cap') :: (if b =? 0 then LBs else as_lb_remove H pid LBs)) m1 mo1
                     (set_v2A c (b', xs ++ [x], cap')) ins tbl ftbl TB spal).
      { pose proof (pmxa_vgrow2b w s LB LBs m mo c ins tbl ftbl TB spal s1 m1 mo1 pid pid' b' x OK X Hknn Hfk) as VGR.
        rewrite EV2 in VGR. cbn [t3a t3b t3c fst snd] in VGR. fold cap' in VGR.
        apply VGR; [exact XSL | exact PIDin | apply (BUD' XSL) | exact RH1 | exact MP1 | exact MI1 | exact ST1 | exists errv1; exact ER1 | exact RA1
                | exact XP1 | exact ABR1 | exact VEC1 | rewrite XSL in SH1; exact SH1 | exact WV1 | exact RF1 | exact AC1' | exact S01 | exact AL1]. }
      eapply (K ms1 mo1 m1 _ s1 _ _ b' cap'); [exact KR1 | exact VIS1 | apply rfull_mkR | exact X1 | | apply (BUD' XSL) | right; split; [exact XSL | split; [reflexivity | exact ABR1]] |].
      + intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
      + intros k cs Hk Hkc RWk.
        exact (vx_ff_keep H HHbp w s LB m m1 O_V2 b (4 * cap) pid [] k cs OK RH RF1 ltac:(apply Forall_nil) ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia) INbLB ltac:(lia) ltac:(rewrite app_nil_r; exact XP1) Hk Hkc RWk).
  Qed.
End VP2b.
