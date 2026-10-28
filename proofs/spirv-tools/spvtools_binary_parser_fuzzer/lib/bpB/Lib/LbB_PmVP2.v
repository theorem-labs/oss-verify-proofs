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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmGlue LbB_PmVops LbB_PmDS LbB_PmWKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmLeaf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require PmStepS1 PmBody1S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmLH LbB_PmU2K LbB_PmU2B_F.

Definition RT_F08EC : list (reg * expr) := (22%bv, EAlu ALU_ADD (EVar 41) (ELit 4)) :: (23%bv, EVar 41) :: RT_F08E8.
Definition RT_VPE : list (reg * expr) := (22%bv, EVar 41) :: RT_F0950.
Definition KN_VP (v a : Z) : list kentry :=
  [KRange (EVar 41) 1 (2 ^ 47); KAlign (EVar 41) a;
   KWord (SA (EAlu ALU_SRL (EVar 41) (ELit 3)) SHBASE) 1 (ELit v);
   KWord (SA (EVar WV_FF) 9120) 4 (EVar 42);
   KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (ELit 3)) SHBASE) 1 (ELit 0);
   KWord (SA (EVar WV_S1) 624) 8 (EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   KWord (SA (EVar WV_S1) 648) 8 (EVar WV_P);
   KWr (SA (EVar WV_P) 0) (ELit 288); KWr (SA (EVar 41) 0) (ELit 4)].

Lemma vp_w4 : forall v, 0 <= v < 2 ^ 32 ->
  word_to_le_bytes 4 (ext_val true 0 4 (Z_to_bv 64 v)) = word_to_le_bytes 4 (Z_to_bv 64 v).
Proof. intros v Hv. rewrite PmStepS1.ext_val_sx4 by lia. apply PmBody1S1.w2lb4_sx32. lia. Qed.

Lemma vp_ar_b8 : forall b, b mod 16 = 0 -> b mod 8 = 0.
Proof. intros b Hb. Z.div_mod_to_equations. lia. Qed.

Lemma vp_ar_e4 : forall b n e, e = b + 4 * n -> b mod 16 = 0 -> e mod 4 = 0.
Proof. intros b n e -> Hb. Z.div_mod_to_equations. lia. Qed.

Lemma vp_ar_emc : forall b n e, e = b + 4 * n -> b mod 16 = 0 -> e mod 8 = 0 \/ e mod 8 = 4.
Proof. intros b n e -> Hb. Z.div_mod_to_equations. lia. Qed.

Lemma vp_ar_ix0 : forall b n e, e = b + 4 * n -> b mod 8 = 0 -> e mod 8 = 0 ->
  (e - b) / 8 = (4 * n + 4) / 8 /\ (4 * n + 4) mod 8 = 4.
Proof. intros b n e -> Hb He. split; Z.div_mod_to_equations; lia. Qed.

Lemma vp_ar_ix4 : forall b n e, e = b + 4 * n -> 0 <= n -> b mod 8 = 0 -> e mod 8 = 4 ->
  (Z.to_nat ((e - b) / 8) < Z.to_nat ((4 * n + 4) / 8))%nat.
Proof. intros b n e -> Hn Hb He. apply Z2Nat.inj_lt; Z.div_mod_to_equations; lia. Qed.

Lemma vp_ar_rng : forall b n e cap, e = b + 4 * n -> 0 <= n < cap -> b <= e < b + 8 * nsh (4 * cap).
Proof. intros b n e cap -> Hn. unfold nsh. Z.div_mod_to_equations. lia. Qed.

Lemma vp_ar_sh248 : forall P b k, 0 <= P -> sh P + nsh 288 <= b \/ b + k <= sh P ->
  (P + 248) / 8 + SHBASE + 1 <= b \/ b + k <= (P + 248) / 8 + SHBASE.
Proof. intros P b k HP D. unfold sh, nsh, ASHADOW_BASE in D. unfold SHBASE. Z.div_mod_to_equations. lia. Qed.

Definition vpF (P : Prop) : Prop := P.
Ltac vp_frz X := let T := type of X in change (vpF T) in X.

Ltac vp_est w e E32 E33 E35 E41 :=
  lazymatch goal with
  | |- estart _ (SA (EVar 32) ?o) = _ => apply (estart_var _ 32 o (wa_p w) E32); lia
  | |- estart _ (SA (EVar 33) ?o) = _ => apply (estart_var _ 33 o (wa_ff w) E33); lia
  | |- estart _ (SA (EVar 35) ?o) = _ => apply (estart_var _ 35 o (wa_s1 w) E35); lia
  | |- estart _ (SA (EVar 41) ?o) = _ => apply (estart_var _ 41 o e E41); lia
  | |- estart _ (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit ?k)) (ELit 3)) _) = _ =>
      apply (estart_sh _ _ (wa_p w + k)); [eapply ev_add; [exact E32 | lia | lia] | lia]
  end.

Ltac vp_sc w e E32 E33 E35 E41 :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCFlat _ (ELit _)) =>
      eapply sc_flat_lit; [vp_est w e E32 E33 E35 E41 | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCDisj _ (ELit _) _ (ELit _)) =>
      eapply sc_disj_lit; [vp_est w e E32 E33 E35 E41 | apply elit_u; lia | vp_est w e E32 E33 E35 E41 | apply elit_u; lia
                          | lia | lia | lia | lia | lia | lia | lia]
  end.

Ltac vp_go HHH MI KR VIS RF HT Xs HK :=
  lazymatch type of HK with know_ok _ _ _ ?kn =>
    pm_goR0 HHH MI KR VIS RF HT Xs kn HK 80%nat [0xf0950] (@nil bool) 43%N RT_VPE end.

Section VP2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Let HHp : asan_rt_hyps H := rt_bp_base H HHbp.

  Lemma pm_vpush2 : forall (w : pmwA H) s LB LBs m mo c TB spal msF R F fc (x : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F08EC [] TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AANNOTATE_CC) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_F08E8 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (t3a (c_v2 c)) ->
    PropExec.getr R 11%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * t3c (c_v2 c)) ->
    PropExec.getr R 12%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) ->
    PropExec.getr R 13%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)) + 4) ->
    PropExec.getr R 22%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)) + 4) ->
    PropExec.getr R 23%bv = Z_to_bv 64 (t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c))) ->
    Zlen (t3b (c_v2 c)) < t3c (c_v2 c) ->
    rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 x)] -> 0 <= x < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1,
       HS_F0950 H LINV w s LB LBs m1 mo1 (set_v2A c (t3a (c_v2 c), t3b (c_v2 c) ++ [x], t3c (c_v2 c))) TB spal msF1 R1 F fc ->
       ffkeep w m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c TB spal msF R F fc x Q OK X KR VIS RF HT0 G3 G4 G10 G11 G12 G13 G22 G23 HCAP Cx Hx K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (xp_geom H HHp w OK) as (XG1 & XG2 & XG3 & XG4 & XG5 & XG6 & _).
    pose proof (p_apart_ff H w OK) as PAF.
    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V2.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as ((_ & _ & _ & _ & SHV2 & _) & ADP & _).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as OWN.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    pose proof (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SLOTS.
    pose proof (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as PDEF.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 _].
    destruct (c_v2 c) as [[b xs] cap] eqn:EV2. cbn [t3a t3b t3c fst snd] in *.
    destruct V2 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE).
    unfold O_V2, PARSER_SIZE in *.
    destruct Hb as [[B0 C0] | (Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia |].
    set (e := b + 4 * Zlen xs) in *.
    assert (Ee : e = b + 4 * Zlen xs) by reflexivity.
    pose proof (Zlen_nonneg xs) as ZL0.
    assert (BLK : exists pid, In (pid, b, 4 * cap) LBs /\ In (pid, b, 4 * cap) LB /\ In (b, 4 * cap) (lbl LB)
                              /\ ablock_range H b (4 * cap) /\ 4 * cap <= 2 ^ 31).
    { apply (cblk_facts H HHp LINV w s LB LBs m mo c _ _ _ TB spal b (4 * cap) OK X).
      unfold c_blocks. rewrite EV2. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; right; right; right; left.
      destruct (Z.eqb_spec b 0); [lia | left; reflexivity]. }
    destruct BLK as (pid & INs & INL & INl & (R0 & R16 & Rn & RI & RC & RF' & RAPP) & SZ).
    pose proof (aapp_bounds _ _ RAPP ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5).
    pose proof (aapp_bounds _ _ XG6 ltac:(lia)) as (FB1 & FB2 & FB3 & FB4 & FB5).
    pose proof (aapp_bounds _ _ PA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    pose proof (blk_apart_ff H HHp w s LB m (pid, b, 4 * cap) OK RH INL) as BAF. cbn [blk_addr blk_size fst snd] in BAF.
    pose proof (blksh_apart_ff H HHp w s LB m pid b (4 * cap) OK RH INL) as (BF1 & BF2).
    pose proof (blk_apart_p H HHp w s LB m b (4 * cap) OK RH INl) as BAP. unfold PARSER_SIZE, O_WIDX in BAP, PAF.
    pose proof (aapp_disjoint_sh b (4 * cap) b (4 * cap) RAPP ltac:(lia) ltac:(lia) ltac:(lia)) as DSHB.
    pose proof (aapp_disjoint_sh b (4 * cap) (wa_p w) 288 RAPP ltac:(lia) ltac:(lia) ltac:(lia)) as DSHP.
    pose proof (aapp_disjoint_sh (wa_p w) 288 b (4 * cap) PA ltac:(lia) ltac:(lia) ltac:(lia)) as DPSH.
    pose proof (sh_apart b (4 * cap) (wa_p w) 288 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHBP.
    assert (SHE : sh b + nsh (4 * cap) <= sh aceil) by (apply sh_end_le; lia).
    assert (SHEP : sh (wa_p w) + nsh 288 <= sh aceil) by (apply sh_end_le; lia).
    assert (SHA : sh aceil <= aceil) by apply sh_aceil_le.
    assert (B8 : b mod 8 = 0) by exact (vp_ar_b8 b B16).
    assert (E4 : e mod 4 = 0) by exact (vp_ar_e4 b (Zlen xs) e Ee B16).
    assert (NSHC : 0 <= nsh (4 * cap)) by (unfold nsh; apply Z.div_pos; lia).

    eapply (pm_annot H HHbp w s msF mo R F fc m b (4 * cap) (4 * Zlen xs) (4 * Zlen xs + 4) _ Q OK KR VIS RF);
      [ exact G10 | exact G11 | exact G12 | rewrite G13; f_equal; lia | rtf HT0 | rtf HT0 | reflexivity | lia
      | exact B8 | lia | lia | lia | exact RAPP | exact (SHV2 ltac:(cbn; lia)) | exact STK1
      | exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | ].
    intros msF2 mo2 m2 R2 KR2 MP2 VIS2 RF2 MU2 WM2 MI2 STK2 SH2 ACm2 KEEP2.
    unfold AINTRIN_STACK in MU2.
    assert (Cx2 : rw_cells asegs m2 (wa_ff w + 9120) [C4 (Z_to_bv 64 x)]).
    { eapply rw_cells_transport; [exact Cx | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Z.of_nat].
      split; [lia | split; [lia | exact I]]. }
    assert (SLOT2 : forall k ex, In (k, ex) TBL_F08EC -> 0 <= k -> k + 8 <= 832 ->
                      rw_cells asegs m2 (wa_s1 w + k) [C8 (edenot (Eseed bvmap_empty (wenv_vals w)) ex)]).
    { intros k ex Hin Hk0 Hk8. unfold slots_ok in SLOTS. rewrite Forall_forall in SLOTS.
      pose proof (SLOTS (k, ex) Hin) as S0. cbn [fst snd] in S0.
      eapply rw_cells_transport; [exact S0 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Z.of_nat].
      split; [lia | split; [lia | exact I]]. }
    assert (ADP2 : addressable m2 (wa_p w) 288).
    { eapply addressable_transport; [exact ADP | exact MU2 | exact WM2 |]. cbn [disjoint_from].
      split; [lia | split; [lia | exact I]]. }
    assert (WRP2 : wr_at asegs m2 (wa_p w) 288).
    { pose proof (wr_at_of_mdef m (wa_p w) 288 0 288 PDEF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as W0.
      rewrite Z.add_0_r in W0. exact (wr_at_wmono _ _ _ _ W0 WM2). }
    assert (WRB : wr_at asegs m b (4 * cap)) by exact (lb_own_In LBs m (pid, b, 4 * cap) OWN INs).
    assert (WRE2 : wr_at asegs m2 e 4).
    { apply (wr_at_sub asegs m2 b (4 * cap) e 4); [exact (wr_at_wmono m m2 b (4 * cap) WRB WM2) | lia | lia | lia]. }
    assert (DM2 : forall y, m y <> None -> m2 y <> None).
    { apply (annot_dm m m2 b (4 * cap) (cc_gen (4 * cap) (4 * Zlen xs + 4)) (wa_lo w) (wa_s1 w - 4096) (wa_s1 w) MU2 SH2);
        [rewrite cc_gen_length by lia; reflexivity | exact STK2 | lia | lia | lia | lia]. }
    assert (SHK : forall v, (v = 4 /\ e mod 8 = 0 \/ v = 0 /\ e mod 8 = 4) -> shk m2 e v).
    { intros v Hvv.
      assert (RNG : b <= e < b + 8 * Z.of_nat (length (cc_gen (4 * cap) (4 * Zlen xs + 4)))).
      { rewrite cc_gen_length by lia. exact (vp_ar_rng b (Zlen xs) e cap Ee ltac:(lia)). }
      destruct (shk_of_SHAD m2 b _ e SH2 RNG) as (bb & Hnth & Hk).
      destruct Hvv as [(-> & EM) | (-> & EM)].
      - destruct (vp_ar_ix0 b (Zlen xs) e Ee B8 EM) as [IX MD].
        pose proof (LbB_PmLeaf.cc_gen_nth_part (4 * cap) (4 * Zlen xs + 4) ltac:(lia) ltac:(rewrite MD; discriminate)) as NP.
        rewrite MD in NP. rewrite IX in Hnth. assert (EB : Some bb = Some (b8 4)) by (rewrite <- Hnth; exact NP).
        injection EB as ->. assert (U4 : bv_unsigned (b8 4) = 4) by reflexivity. rewrite U4 in Hk. exact Hk.
      - pose proof (vp_ar_ix4 b (Zlen xs) e Ee ZL0 B8 EM) as IX.
        pose proof (LbB_PmTac.cc_gen_nth0 (4 * cap) (4 * Zlen xs + 4) (Z.to_nat ((e - b) / 8)) ltac:(lia) IX) as NP.
        assert (EB : Some bb = Some (b8 0)) by (rewrite <- Hnth; exact NP).
        injection EB as ->. assert (U0 : bv_unsigned (b8 0) = 0) by reflexivity. rewrite U0 in Hk. exact Hk. }
    pose proof (vp_ar_sh248 (wa_p w) b (4 * cap) ltac:(lia) DSHP) as SHP248.
    pose proof (shaddr_bounds (wa_p w + 248) ltac:(unfold AAPP_HI in *; lia)) as SB248.

    set (Xs := [Z_to_bv 64 e; Z_to_bv 64 x]).
    assert (KP8 : forall r, In r (map fst RT_F08E8) -> In r KEPT_REGS).
    { intros r Hr. cbn [map fst RT_F08E8] in Hr. repeat (destruct Hr as [<-|Hr]; [inb|]). destruct Hr. }
    assert (HT2 : regs_tblX w Xs R2 RT_F08EC).
    { unfold RT_F08EC. apply regs_tbl_cons; [| apply regs_tbl_cons].
      - rewrite (KEEP2 22%bv ltac:(inb)), G22. symmetry. apply ev_add; [ev_xs; reflexivity | lia | lia].
      - rewrite (KEEP2 23%bv ltac:(inb)), G23. symmetry. ev_xs. reflexivity.
      - pose proof (regs_tbl_ext w [] Xs R RT_F08E8 HT0 ltac:(vm_compute; reflexivity)) as HTx.
        unfold regs_tblX in HTx |- *. rewrite Forall_forall in HTx |- *. intros [r ex] Hin. cbn [fst snd] in *.
        rewrite (KEEP2 r (KP8 r (in_map fst _ _ Hin))). exact (HTx (r, ex) Hin). }
    pose proof (env_world_seed H w R2 Xs) as HE2.
    pose proof (ev_world_all H w _ HE2) as (EV32 & EV33 & _ & EV35 & _).
    assert (EV41 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 e) by (ev_xs; reflexivity).
    assert (EV42 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 x) by (ev_xs; reflexivity).
    assert (EV41u : bv_unsigned (edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 41)) = e) by (rewrite EV41, u64_of_Z by lia; reflexivity).
    assert (SL624 : In (624, EAlu ALU_ADD (EVar WV_FF) (ELit 9040)) TBL_F08EC).
    { unfold TBL_F08EC, TBL_F0884. cbn [app]. repeat first [apply in_eq | apply in_cons]. }
    assert (SL648 : In (648, EVar WV_P) TBL_F08EC).
    { unfold TBL_F08EC, TBL_F0884. cbn [app]. repeat first [apply in_eq | apply in_cons]. }
    assert (HKV : forall v a, (v = 4 /\ a = 8 /\ e mod 8 = 0 \/ v = 0 /\ a = 4 /\ e mod 8 = 4) ->
              know_ok asegs (Eseed R2 (wenv_vals w ++ Xs)) m2 (KN_VP v a)).
    { intros v a Hva. unfold know_ok, KN_VP.
      repeat apply Forall_cons; try apply Forall_nil.
      - cbn [kentry_ok]. rewrite EV41u. unfold AAPP_HI in *. lia.
      - cbn [kentry_ok]. rewrite EV41u. destruct Hva as [(-> & -> & EM)|(-> & -> & EM)]; split; first [lia | exact EM | exact E4].
      - apply (kshadow _ m2 (EVar 41) e v (ELit v) EV41 ltac:(lia));
          [destruct Hva as [(-> & _)|(-> & _)]; lia | reflexivity |].
        apply SHK. destruct Hva as [(-> & _ & EM)|(-> & _ & EM)]; [left|right]; split; auto.
      - apply (kword_of_rw_cells asegs _ m2 (wa_ff w + 9120) [C4 (Z_to_bv 64 x)] 0 (C4 (Z_to_bv 64 x)) _ _ 4 Cx2 eq_refl eq_refl
                 ltac:(lia)); [| lia | lia | rewrite EV42; reflexivity].
        transitivity (wa_ff w + 9120); [apply (estart_var _ 33 9120 (wa_ff w) EV33); lia | cbn; lia].
      - apply (kshadow0 _ m2 (EAlu ALU_ADD (EVar WV_P) (ELit 248)) (wa_p w + 248)); [apply ev_add; [exact EV32 | lia | lia] | lia |].
        apply (sh0_of_addressable m2 (wa_p w) 288); [exact ADP2 | change (8 * (288 / 8)) with 288; lia].
      - apply (kslot_of_cells H w _ m2 624 (EAlu ALU_ADD (EVar WV_FF) (ELit 9040)) OK HE2 eq_refl);
          [apply SLOT2; [exact SL624 | lia | lia] | lia | lia].
      - apply (kslot_of_cells H w _ m2 648 (EVar WV_P) OK HE2 eq_refl); [apply SLOT2; [exact SL648 | lia | lia] | lia | lia].
      - assert (EZ : elenZ (Eseed R2 (wenv_vals w ++ Xs)) (ELit 288) = 288) by (apply elit_u; lia).
        apply (kwr_of_wr_at asegs _ m2 (wa_p w) 288); [exact WRP2 | | | ];
          rewrite ?(estart_p H w _ 0 OK HE2), ?EZ; lia.
      - assert (EZ : elenZ (Eseed R2 (wenv_vals w ++ Xs)) (ELit 4) = 4) by (apply elit_u; lia).
        assert (ES : estart (Eseed R2 (wenv_vals w ++ Xs)) (SA (EVar 41) 0) = e + 0) by (apply (estart_var _ 41 0 e EV41); lia).
        apply (kwr_of_wr_at asegs _ m2 e 4); [exact WRE2 | | | ]; rewrite ?ES, ?EZ; lia. }

    vp_frz Q6. vp_frz BAF. vp_frz BF1. vp_frz BF2. vp_frz BAP. vp_frz PAF. vp_frz DSHB. vp_frz DSHP. vp_frz DPSH.
    vp_frz SHBP. vp_frz Bapart.
    enough (RUNK : forall msF3 mo3 R3 m3, as_AKREL H s (mkCfg msF3 mo3) -> as_MPRES H mo2 mo3 ->
              as_VIS H s msF3 = MS R3 F (Z_to_bv 64 0xf0950) fc None m3 (seg_rom asegs) -> rfull R3 -> mem_inv asegs m3 ->
              regs_tblX w Xs R3 RT_VPE -> PropExec.getr R3 3%bv = wa_gp w -> PropExec.getr R3 4%bv = wa_tp w ->
              munch [(wa_p w + 248, wa_p w + 256); (e, e + 4)] m2 m3 -> wmono asegs m2 m3 ->
              (forall y, m2 y <> None -> m3 y <> None) -> stk asegs m3 (wa_lo w) (wa_s1 w) ->
              rw_cells asegs m3 (wa_p w + 248) [C8 (Z_to_bv 64 (e + 4))] -> rw_cells asegs m3 e [C4 (Z_to_bv 64 x)] ->
              as_SR H Q (mkCfg msF3 mo3)).
    { assert (Y41 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EVar 41) (ELit 4)) = Z_to_bv 64 (e + 4))
        by (apply ev_add; [exact EV41 | lia | lia]).
      pose proof (vp_ar_emc b (Zlen xs) e Ee B16) as EMC.
      destruct EMC as [EM|EM];
        [pose proof (HKV 4 8 ltac:(left; repeat split; exact EM)) as HK2
        |pose proof (HKV 0 4 ltac:(right; repeat split; exact EM)) as HK2].
      all: vp_go HHp MI2 KR2 VIS2 RF2 HT2 Xs HK2;
             [ first [ apply Forall_nil | split_scs; vp_sc w e EV32 EV33 EV35 EV41 ] | ].
      all: intros msF3 mo3 R3 KR3 MP3 VIS3 RF3 MI3 HT3 HR3 Hlf3.
      all: subst SSr; cbn [s_pc s_log] in VIS3, MI3, Hlf3.
      all: apply (RUNK msF3 mo3 R3 _ KR3 MP3 VIS3 RF3 MI3 HT3);
             [ rewrite (HR3 3%bv); change (PropExec.getr R2 3%bv = wa_gp w); rewrite (KEEP2 3%bv ltac:(inb)); exact G3
             | rewrite (HR3 4%bv); change (PropExec.getr R2 4%bv = wa_tp w); rewrite (KEEP2 4%bv ltac:(inb)); exact G4
             | pose proof (munch_sym _ m2 _ [(EVar WV_P, 248, 256); (EVar 41, 0, 4)] Hlf3 ltac:(vm_compute; reflexivity)) as MU;
               cbn [num_wins map] in MU; rewrite (ev_p H w _ OK HE2), EV41u, Z.add_0_r in MU; exact MU
             | apply wmono_mem_denot
             | intros y Hy; apply mem_denot_defined; exact Hy
             | apply stk_mem_denot; exact STK2
             | apply (rw_cells_mem_denot_w _ m2 [] (SA (EVar 32) 248) 8 (EAlu ALU_ADD (EVar 41) (ELit 4)) _ (wa_p w + 248)
                        (C8 (Z_to_bv 64 (e + 4))));
               [ exact Hlf3 | apply Forall_nil | apply (estart_var _ 32 248 (wa_p w) EV32); lia
               | apply (wr_at_sub asegs m2 (wa_p w) 288); [exact WRP2 | lia | lia | lia] | reflexivity | exact I
               | rewrite Y41; reflexivity ]
             | apply (rw_cells_mem_denot_w _ m2 [SE (SA (EVar 32) 248) 8 (EAlu ALU_ADD (EVar 41) (ELit 4))] (SA (EVar 41) 0) 4
                        (EExt true 0 4 (EVar 42)) [] e (C4 (Z_to_bv 64 x)));
               [ exact Hlf3
               | apply Forall_cons; [| apply Forall_nil]; cbn [e_addr e_width Z.of_nat];
                 rewrite (estart_var _ 32 248 (wa_p w) EV32), (estart_var _ 41 0 e EV41) by lia; unfold vpF in BAP; lia
               | rewrite (estart_var _ 41 0 e EV41) by lia; lia
               | exact WRE2 | reflexivity | exact I
               | change (edenot ?E (EExt true 0 4 (EVar 42))) with (ext_val true 0 4 (edenot E (EVar 42)));
                 rewrite EV42, vp_w4 by lia; reflexivity ] ]. }

    intros msF3 mo3 R3 m3 KR3 MP3 VIS3 RF3 MI3 HT3 G3_3 G4_3 MU3 WM3 DM3 STK3 RWE RWX.
    assert (MUA : munch ([(sh b, sh b + nsh (4 * cap)); (e, e + 4); (wa_p w + 248, wa_p w + 256)] ++ [(wa_s1 w - 4096, wa_s1 w)]) m m3).
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU2 MU3)].
      intros y Hy. cbn [outside app] in Hy |- *. destruct Hy as (N1 & N2 & N3 & N4 & _).
      repeat split; first [exact N1 | exact N2 | exact N3 | exact N4]. }
    assert (WMA : wmono asegs m m3) by exact (wmono_trans _ _ _ _ WM2 WM3).
    assert (X3 : PMXAT H LINV w s LB LBs m3 mo3 (set_v2A c (b, xs ++ [x], cap)) [OB_INST; OB_FIRST_WORD] TBL_F08EC [] TB spal).
    { replace (b, xs ++ [x], cap) with (t3a (c_v2 c), xs ++ [x], t3c (c_v2 c)) by (rewrite EV2; reflexivity).
      eapply (pmxa_vupd2 H HHp LINV LINV_frame w s LB LBs m mo c _ _ _ TB spal m3 mo3);
        [ exact OK | exact X | vm_compute; reflexivity | reflexivity | exact MUA | exact WMA
        | intros y Hy; apply DM3; apply DM2; exact Hy
        | exact (ah_mpres_trans H HHp _ _ _ MP2 MP3)
        | exact MI3 | exact STK3 | | | | ].
      - unfold vwin, blkV2. rewrite EV2. cbn [t3a t3c fst snd]. unfold O_V2.
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
        + split; [lia|]. right; right. split; [lia | lia].
        + split; [lia|]. right; left. split; [lia | lia].
        + split; [lia|]. left. lia.
      - apply Forall_cons; [| apply Forall_nil]. unfold swin. cbn [fst snd]. lia.
      - rewrite EV2. cbn [t3a t3c fst snd]. unfold vec32, O_V2.
        split; [exact Hv|]. split; [exact Hv'|].
        split; [intros i Hi; apply DM3; apply DM2; apply HD; lia|].
        split; [rewrite Zlen_app1; lia|].
        split; [unfold vpF in Bapart; right; repeat split; assumption|].
        split; [eapply (fld_munch _ m m3); [exact F0 | exact MUA | cbn [disjoint_from app]; unfold vpF in DPSH, BAP; repeat split; lia | lia | lia]|].
        split.
        { replace (b + 4 * Zlen (xs ++ [x])) with (bv_unsigned (Z_to_bv 64 (e + 4))) by (rewrite u64_of_Z, Zlen_app1; lia).
          replace (wa_p w + 240 + 8) with (wa_p w + 248) by lia. apply fld_of_cell8; [exact RWE | lia]. }
        split; [eapply (fld_munch _ m m3); [exact F2 | exact MUA | cbn [disjoint_from app]; unfold vpF in DPSH, BAP; repeat split; lia | lia | lia]|].
        intros i Hi. rewrite Zlen_app1 in Hi. destruct (Z.eq_dec i (Zlen xs)) as [->|Hne].
        + rewrite Znth_app_r1. split; [lia|]. change (b + 4 * Zlen xs) with e.
          pose proof (fld_of_cell4 m3 e (Z_to_bv 64 x) RWX ltac:(lia)) as FX. rewrite u64_of_Z in FX by lia. exact FX.
        + rewrite Znth_app_l by lia. destruct (FE i ltac:(lia)) as [FE1 FE2]. split; [exact FE1|].
          eapply (fld_munch _ m m3); [exact FE2 | exact MUA | cbn [disjoint_from app]; unfold vpF in DSHB, BAP; repeat split; lia | lia | lia].
      - rewrite EV2. unfold vsh32. cbn [t3a t3b t3c fst snd]. intros _.
        replace (4 * Zlen (xs ++ [x])) with (4 * Zlen xs + 4) by (rewrite Zlen_app1; lia).
        eapply SHAD_transport; [exact SH2 | exact MU3 | exact WM3 |].
        rewrite cc_gen_length by lia. cbn [disjoint_from]. unfold vpF in DPSH, DSHB. split; [lia | split; [lia | exact I]]. }
    pose proof HT3 as HT3'. unfold RT_VPE, regs_tblX in HT3'. apply Forall_cons_iff in HT3' as [Y22 HT3']. cbn [fst snd] in Y22.
    pose proof (regs_tbl_restrict w [] Xs R3 RT_F0950 HT3' ltac:(vm_compute; reflexivity)) as HTF.
    apply (K msF3 mo3 m3 R3).
    - constructor.
      + exact X3.
      + exact KR3.
      + exact VIS3.
      + exact RF3.
      + exact HTF.
      + exact G3_3.
      + exact G4_3.
      + cbn [set_v2A c_v2 t3a t3b t3c fst snd]. rewrite Zlen_app1, Y22. ev_xs. f_equal. lia.
    - apply (ffkeep_munch w _ m m3 MUA WMA). cbn [app]. unfold vpF in BF1, BAF, PAF.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]; cbn [fst snd]; lia.
  Qed.
End VP2.
