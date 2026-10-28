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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmVops LbB_PmVup LbB_TablStmt LbB_PmU2K LbB_HEmpStmt LbB_PmWM LbB_PmWSt LbB_PmWM3 LbB_PmLeaf LbB_StrPb LbB_MkStr LbB_PmStr LbB_PmS8K.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section SW3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  #[local] Notation ent := (Z * (Z * Z))%type (only parsing).

  Hypothesis HOWN : rt_own H.
  Lemma HHs3 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_sw_m3 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl msF R F fc (bl bc : Z) (l1 l2 : list ent) (q k v v' : Z)
                              (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo (set_m3A c (bl, bc, l1 ++ (q, (k, v)) :: l2)) ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3210) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 10%bv = Z_to_bv 64 (q + 20) -> PropExec.getr R 21%bv = Z_to_bv 64 (sx32A v') -> 0 <= v' < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf3214) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 (set_m3A c (bl, bc, l1 ++ (q, (k, v')) :: l2)) ins tbl ftbl ->
       (forall r, PropExec.getr R1 r = PropExec.getr R r) ->
       (forall kk cs, 0 <= kk -> kk + Z.of_nat (cells_size cs) <= 16384 -> rw_cells asegs m (wa_ff w + kk) cs -> rw_cells asegs m1 (wa_ff w + kk) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl msF R F fc bl bc l1 l2 q k v v' Q OK X Hknn Hfk KR VIS RF G10 G25 Hv' K.
    pose proof HHs3 as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    set (c0 := set_m3A c (bl, bc, l1 ++ (q, (k, v)) :: l2)) in *.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as LBO.

    assert (Hinp : In (q, (k, v)) (l1 ++ (q, (k, v)) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    assert (XBc : In (q, 24) (c_blocks c0)).
    { apply (Permutation_in _ (Permutation_sym (cbk_m3 c0))). apply in_or_app; left. unfold mblk3, c0, set_m3A. cbn [c_m1 c_m2 c_m3 t3a t3b t3c fst snd].
      unfold umap_blocks. apply in_or_app; right. apply in_map_iff. exists (q, (k, v)). split; [reflexivity | exact Hinp]. }
    destruct (xb_facts H HH w s LB LBs [] m c0 (q, 24) OK RH OWN1 OWN2 XBc) as (pid & XB1 & XB2 & XB3 & XBR). cbn [fst snd] in XB1, XB2, XB3, XBR.
    pose proof XBR as (R0 & R16 & Rn & RI & RC & RF' & RAPP).
    assert (WQ : wr_at asegs m q 24) by exact (proj1 (Forall_forall _ _) LBO _ XB1).

    set (Xv := [Z_to_bv 64 (q + 20)]).
    assert (HTv : regs_tblX w Xv R RT_SW).
    { unfold regs_tblX, RT_SW. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. rewrite G10. reflexivity. }
    assert (HE : env_world H w (Eseed R (wenv_vals w ++ Xv))) by apply env_world_seed.
    assert (E41 : edenot (Eseed R (wenv_vals w ++ Xv)) (EVar 41) = Z_to_bv 64 (q + 20)) by reflexivity.
    assert (HK0 : know_ok asegs (Eseed R (wenv_vals w ++ Xv)) m KN_SW).
    { unfold KN_SW, know_ok. apply Forall_cons; [| apply Forall_nil].
      eapply (kwr_of_wr_at _ _ m q 24); [exact WQ | | |]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?E41; cbn [edenot];
        rewrite ?unsigned_lit by lia; lia. }
    pm_goR HH OK X KR VIS RF HTv Xv KN_SW HK0 10%nat [0xf3214] (@nil bool) 42%N (@nil (reg * expr)).
    { split_scs. eapply (sc_flat_lit asegs _ _ _ _ (q + 20 + 0) 4); [apply (estart_var _ 41 0 (q + 20) E41); lia | apply elit_u; lia | lia | lia | lia]. }
    intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1 HR1 Hlf1.
    lazymatch type of VIS1 with _ = MS _ _ _ _ _ ?mm _ => set (M1 := mm) in * end.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ Xv)) m _ [(EVar 41, 0, 4)] Hlf1 ltac:(vm_compute; reflexivity)) as MU1.
    cbn [num_wins map] in MU1. rewrite E41, unsigned_lit in MU1 by lia. rewrite Z.add_0_r in MU1.
    replace (q + 20 + 4) with (q + 24) in MU1 by lia.
    assert (RW1 : rw_cells asegs M1 (q + 20) [C4 (Z_to_bv 64 v')]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat (EVar 41%N) 0 4 (EVar 21));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite E41, u64_of_Z by lia; lia
        | exact (wr_at_subS m q 24 (q + 20) 4 WQ ltac:(lia) ltac:(lia) ltac:(lia))
        | reflexivity | exact Logic.I
        | cbn [cbytes]; change (edenot (Eseed R (wenv_vals w ++ Xv)) (EVar 21)) with (PropExec.getr R 21%bv); rewrite G25; apply w2lb4_sx32A; exact Hv' ]. }
    assert (X1 : PMXA H LINV w s LB LBs M1 mo1 (set_m3A c (bl, bc, l1 ++ (q, (k, v')) :: l2)) ins tbl ftbl).
    { apply (pmxa_mpres H HH LINV w _ _ _ _ mo mo1); [| exact MP1].
      eapply (pm_m3_setval H HHbp LINV LINV_cl w s LB LBs m mo c ins tbl ftbl M1 bl bc l1 l2 q k v v' OK X Hknn Hfk MU1);
        [apply wmono_mem_denot | intros x Hx; apply mem_denot_defined; exact Hx | exact MI1 | exact RW1 | exact Hv']. }
    replace (s_pc SSr) with 0xf3214 in VIS1 by reflexivity.
    eapply (K msF1 mo1 M1 R1 KR1 VIS1 RF1 X1).
    - intros r. rewrite (HR1 r).
      pose proof (regs_ok_of_tbl w R RT_SW Xv (xbound Xv) HTv ltac:(vm_compute; reflexivity)) as HR0.
      replace (s_regs SSr) with (srs sr_id RT_SW) by (vm_compute; reflexivity). symmetry. apply HR0.
    - intros kk cs Hkk Hcs C. eapply rw_cells_transport; [exact C | exact MU1 | apply wmono_mem_denot |].
      cbn [disjoint_from]. split; [| exact I].
      pose proof (blk_apart_ff H HH w s LB m _ OK RH XB2) as BF. cbn [blk_addr blk_size fst snd] in BF. lia.
  Qed.
End SW3.

Lemma Znth_app1_ltI : forall xs x i, 0 <= i < Zlen xs -> Znth i (xs ++ [x]) = Znth i xs.
Proof. intros xs x i Hi. unfold Znth, Zlen in *. apply app_nth1. lia. Qed.
Lemma Znth_app1_eqI : forall xs x, Znth (Zlen xs) (xs ++ [x]) = x.
Proof. intros xs x. unfold Znth, Zlen. rewrite Nat2Z.id. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma In_ZnthI : forall (c : Z) cs, In c cs -> exists i, 0 <= i < Zlen cs /\ Znth i cs = c.
Proof.
  intros c cs Hin. destruct (In_nth cs c 0 Hin) as (n & Hn & E). exists (Z.of_nat n). unfold Zlen, Znth.
  rewrite Nat2Z.id. split; [lia | exact E].
Qed.

Section ITG.
  Context {HCEIL : HeapCeil}.

  Definition itg_preL (x : Z * list byte) (m : mem) (sp : Z) (a0 a1 a2 a3 : word) : Prop :=
    a0 = Z_to_bv 64 (fst x) /\ bytes_at asegs m (fst x) (snd x ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) (snd x) /\
    accessible m (fst x) (Z.of_nat (length (snd x)) + 1) /\ shvis m (fst x) (fst x + Z.of_nat (length (snd x)) + 1) /\
    in_app_mem (fst x) (fst x + Z.of_nat (length (snd x)) + 1) /\ Z.of_nat (length (snd x)) + 1 <= 2 ^ 40 /\
    fst x + Z.of_nat (length (snd x)) + 1 <= aceil.
  Definition itg_postL (x : Z * list byte) (m : mem) (r0 r1 : word) (m' : mem) : Prop :=
    exists r, 0 <= r < 2 ^ 31 /\ r0 = Z_to_bv 64 r.

  Lemma itg_tleaf : import_type_get_stmtA -> tleaf AT_IMPORT_TYPE_GET IT_STACK itg_preL (fun _ => []) itg_postL.
  Proof.
    intros HI [q str] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo STK ACL LO SP16 SP47 MI AC (E0 & BY & NZ & ACC & SHV & APP & L40 & CEIL). cbn [fst snd] in *.
    assert (APT : q + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= q) by (left; lia).
    exact (HI ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m str q lo E0 BY NZ ACC SHV APP L40 APT STK ACL LO SP16 SP47 MI AC).
  Qed.
End ITG.

Section Imp.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Lemma HH : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_leafL : forall {X : Type} (entry STK : Z) (PRE : X -> mem -> Z -> word -> word -> word -> word -> Prop)
      (Wf : X -> list (Z * Z)) (Qf : X -> mem -> word -> word -> mem -> Prop),
    tleaf entry STK PRE Wf Qf ->
    forall (x : X) (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 entry) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= STK <= 16384 -> Wf x = [] ->
    PRE x m (wa_s1 w) (PropExec.getr R 10%bv) (PropExec.getr R 11%bv) (PropExec.getr R 12%bv) (PropExec.getr R 13%bv) ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c ins tbl ftbl TB spal ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       munch [(wa_s1 w - STK, wa_s1 w)] m m1 -> wmono asegs m m1 ->
       Qf x m (PropExec.getr R1 10%bv) (PropExec.getr R1 11%bv) m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros X entry STK PRE Wf Qf HL x w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q OK XA KR VIS RF
           G2 G1 Hret2 Hret HSTK HW HPRE Ht Hfk K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (wk_s1 H w OK) as (S7 & S8).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (p_apart_ff H w OK) as PAF.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA) as STK0.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK0 ltac:(lia)) as [STK1 STK2].
    rewrite (rfull_eq R RF) in VIS.
    eapply (ahh_evt_then H HH _); [exact KR | exact VIS | |].
    { eapply (HL x (PropExec.getr R 1%bv) (PropExec.getr R 2%bv) (PropExec.getr R 3%bv) (PropExec.getr R 4%bv)
                 (PropExec.getr R 5%bv) (PropExec.getr R 6%bv) (PropExec.getr R 7%bv) (PropExec.getr R 8%bv)
                 (PropExec.getr R 9%bv) (PropExec.getr R 10%bv) (PropExec.getr R 11%bv) (PropExec.getr R 12%bv)
                 (PropExec.getr R 13%bv) (PropExec.getr R 14%bv) (PropExec.getr R 15%bv) (PropExec.getr R 16%bv)
                 (PropExec.getr R 17%bv) (PropExec.getr R 18%bv) (PropExec.getr R 19%bv) (PropExec.getr R 20%bv)
                 (PropExec.getr R 21%bv) (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) (PropExec.getr R 24%bv)
                 (PropExec.getr R 25%bv) (PropExec.getr R 26%bv) (PropExec.getr R 27%bv) (PropExec.getr R 28%bv)
                 (PropExec.getr R 29%bv) (PropExec.getr R 30%bv) (PropExec.getr R 31%bv) F fc m (wa_lo w)).
      - rewrite G2, u64_of_Z by lia. exact STK1.
      - exact S1.
      - rewrite G2, u64_of_Z by lia. unfold APM_STACK in *. lia.
      - rewrite G2, u64_of_Z by lia. rewrite <- (Z.mul_1_l 16) at 1. clear - S8. Z.div_mod_to_equations. lia.
      - rewrite G2, u64_of_Z by lia. unfold AAPP_HI in *. lia.
      - exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA).
      - exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA).
      - rewrite G2, u64_of_Z by lia. exact HPRE. }
    intros msF1 mo1 KR1 MP1 POST.
    destruct POST as (t0 & t1 & t2 & a0' & a1' & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & VIS1 & MU & WM & MI & STK' & AC' & QQ).
    rewrite HW in MU. rewrite G2 in MU, STK'. rewrite !u64_of_Z in MU by lia. rewrite !u64_of_Z in STK' by lia.
    rewrite G1 in VIS1. rewrite (ret_pc_even ret Hret Hret2) in VIS1.
    set (W := [(wa_s1 w - STK, wa_s1 w)]) in MU.
    assert (DM : forall y, m y <> None -> m' y <> None).
    { intros y Hy. destruct (outside_dec W (bv_unsigned y)) as [Ho|(lo' & hi' & Hin & Hr)].
      - rewrite (MU y Ho). exact Hy.
      - pose proof (bv_unsigned_in_range 64 y) as Ry. change (bv_modulus 64) with (2 ^ 64) in Ry.
        rewrite <- (Z_to_bv_bv_unsigned y). subst W.
        destruct Hin as [Hin|[]]. injection Hin as <- <-.
        destruct STK' as (_ & _ & SS). destruct (SS (bv_unsigned y) ltac:(unfold APM_STACK in *; lia)) as [_ (b & Hb)].
        unfold wa in Hb. exact (def_of_mrd_hi m' (bv_unsigned y) _ ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) Hb). }
    assert (STK'' : stk asegs m' (wa_lo w) (wa_sp0 w)).
    { apply (stk_join m' (wa_lo w) (wa_s1 w) (wa_sp0 w)); [exact STK' | | lia].
      eapply (stk_transport_disjoint asegs W m m' (wa_s1 w) (wa_sp0 w) STK2 MU WM).
      subst W. cbn [disjoint_from]. split; [lia | exact I]. }
    assert (X1 : PMXAT H LINV w s LB LBs m' mo c ins tbl ftbl TB spal).
    { eapply (pmxa_munch H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m' W tbl ftbl OK XA MU WM DM MI STK'').
      - subst W. apply Forall_cons; [left; cbn [fst snd]; unfold APM_STACK in *; lia | apply Forall_nil].
      - subst W. apply Forall_cons; [cbn; lia | apply Forall_nil].
      - subst W. cbn [disjoint_from]. unfold PM_NSH in *. rewrite Q13 in *.
        split; [left; lia | exact I].
      - subst W. cbn [disjoint_from]. unfold O_WIDX, O_FLAGS, PARSER_SIZE in *.
        split; [left; lia | exact I].
      - apply incl_refl.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Ht kk (in_map fst _ (kk, e) Hin)) as Kk. apply Z.leb_le in Kk.
        subst W. cbn [disjoint_from]. split; [right; lia | exact I].
      - apply incl_refl.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Hfk kk (in_map fst _ (kk, e) Hin)) as Kb.
        apply andb_true_iff in Kb as [Kb1 Kb2]. apply Z.leb_le in Kb1. apply Z.leb_le in Kb2.
        subst W. cbn [disjoint_from]. split; [left; lia | exact I]. }
    eapply K; [exact KR1 | exact VIS1 | apply rfull_mkR | eapply (pmxa_mpres H HH LINV); [exact X1 | exact MP1] | | exact MU | exact WM | exact QQ].
    intros r Hr.
    repeat (destruct Hr as [<-|Hr]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr.
  Qed.

  Lemma str_src : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal (sb : sbuf) (pid : bptr) (cs : list Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    strA LB m (wa_ff w + 5936) sb cs -> spb_blk LB m sb pid -> obj_sh_ok ins 5936 24 = true ->
    Forall (fun c => c <> 0) cs -> Zlen cs < 2 ^ 28 ->
    itg_preL (str_data (wa_ff w + 5936) sb, str_bytes cs) m (wa_s1 w) (Z_to_bv 64 (str_data (wa_ff w + 5936) sb)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal sb pid cs OK X RP BK Hok NZ HL28.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof RP as (Hs & Hs' & HD & Hlen & HM & HC & HZ).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    set (q := str_data (wa_ff w + 5936) sb) in *.
    assert (LEN : Z.of_nat (length (str_bytes cs)) = Zlen cs) by (rewrite str_bytes_length; reflexivity).
    assert (QR : 0 <= q /\ q + Zlen cs + 1 <= aceil /\ in_app_mem q (q + Zlen cs + 1)).
    { subst q. destruct sb as [|d asz]; cbn [str_data str_cap] in *.
      - unfold SSO_CAP in Hlen. pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
        split; [lia|]. split; [lia|].
        unfold in_app_mem. destruct FA as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi in *;
          unfold ALOWSH_LO, AHI_LO, AAPP_HI, AIMG_TOP, ASHADOW_BASE, AFS_HDR in *; [left | right]; lia.
      - destruct BK as [BIn _]. pose proof (ah_blocks H HH _ _ _ _ RH BIn) as (R0 & R16 & Rn & RI & RC & RF' & RAPP).
        cbn [blk_addr blk_size fst snd] in *. split; [lia|]. split; [lia|].
        unfold in_app_mem. destruct RAPP as [(L1 & L2)|(L1 & L2)]; unfold ALOWSH_LO, AHI_LO, AAPP_HI, AIMG_TOP, ASHADOW_BASE in *; [left | right]; lia. }
    destruct QR as (Q0 & QC & QA).
    unfold itg_preL. cbn [fst snd]. rewrite LEN.
    split; [reflexivity|]. split.
    {
      replace (str_bytes cs ++ [Z_to_bv 8 0]) with (str_bytes (cs ++ [0])) by (rewrite str_bytes_app; reflexivity).
      apply bytes_at_of_rdn; [lia | rewrite str_bytes_length, length_app; cbn [length]; unfold Zlen in *; lia |].
      rewrite str_bytes_length. apply (fld_str_rdn ASEGS); [lia | rewrite Zlen_app1; lia |].
      intros i Hi. rewrite Zlen_app1 in Hi.
      destruct (Z.eq_dec i (Zlen cs)) as [->|Hne].
      - rewrite Znth_app1_eqI. split; [lia | exact HZ].
      - rewrite Znth_app1_ltI by lia. exact (HC i ltac:(lia)). }
    split.
    {
      intros Hin. unfold str_bytes in Hin. apply in_map_iff in Hin as (c0 & E0 & Hc0).
      destruct (In_ZnthI c0 cs Hc0) as (i & Hi & Ei). destruct (HC i Hi) as [Hr _]. rewrite Ei in Hr.
      pose proof (proj1 (Forall_forall _ _) NZ c0 Hc0) as Hnz. cbn beta in Hnz.
      assert (E1 : bv_unsigned (Z_to_bv 8 c0) = c0)
        by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; lia).
      rewrite E0 in E1. assert (E2 : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity. lia. }
    split.
    {
      subst q. destruct sb as [|d asz]; cbn [str_data str_cap] in *.
      - unfold SSO_CAP in Hlen.
        apply (addressable_accessible m (wa_ff w + 5936) 24 (wa_ff w + 5936 + 1) (Zlen cs + 1)); [| lia | lia | unfold AAPP_HI in *; lia].
        exact (ff_addressable m (wa_ff w) ins 5936 24 (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) Hok).
      - destruct BK as [BIn BSH]. pose proof (ah_blocks H HH _ _ _ _ RH BIn) as (R0 & R16 & Rn & RI & RC & RF' & RAPP).
        cbn [blk_addr blk_size fst snd] in *.
        apply (addressable_accessible m d asz d (Zlen cs + 1)); [split; [lia | exact BSH] | lia | lia | unfold AAPP_HI in *; lia]. }
    split.
    {
      subst q. destruct sb as [|d asz]; cbn [str_data str_cap] in *.
      - unfold SSO_CAP in Hlen. replace (wa_ff w + 5936 + 1) with (wa_ff w + 5937) by lia.
        replace (wa_ff w + 5937 + Zlen cs + 1) with (wa_ff w + 5937 + (Zlen cs + 1)) by lia.
        apply (ff_shvis m (wa_ff w) ins 5937 (Zlen cs + 1) (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); unfold AAPP_HI in *; lia.
      - destruct BK as [BIn BSH]. pose proof (ah_blocks H HH _ _ _ _ RH BIn) as (R0 & R16 & Rn & RI & RC & RF' & RAPP).
        cbn [blk_addr blk_size fst snd] in *.
        apply (shvis_sub m d (d + asz)); [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH BIn) | lia | lia | lia | lia | lia]. }
    split; [exact QA|]. split; [lia | lia].
  Qed.

  Lemma pm_import : import_type_get_stmtA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret : Z) (sb : sbuf) (pid : bptr) (cs : list Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_IMPORT_TYPE_GET) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R 10%bv = Z_to_bv 64 (str_data (wa_ff w + 5936) sb) ->
    strA LB m (wa_ff w + 5936) sb cs -> spb_blk LB m sb pid -> obj_sh_ok ins 5936 24 = true ->
    Forall (fun c => c <> 0) cs -> Zlen cs < 2 ^ 28 ->
    (forall msF1 mo1 m1 R1 (r : Z), as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c ins tbl ftbl TB spal ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       munch [(wa_s1 w - IT_STACK, wa_s1 w)] m m1 -> wmono asegs m m1 ->
       0 <= r < 2 ^ 31 -> PropExec.getr R1 10%bv = Z_to_bv 64 r ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HI w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret sb pid cs Q OK X Hknn Hfk KR VIS RF G1 Hr2 Hr G2 G10 RP BK Hok NZ HL28 K.
    pose proof (str_src w s LB LBs m mo c ins tbl ftbl TB spal sb pid cs OK X RP BK Hok NZ HL28) as PRE.
    eapply (pm_leafL AT_IMPORT_TYPE_GET IT_STACK itg_preL (fun _ => []) itg_postL (itg_tleaf HI)
              (str_data (wa_ff w + 5936) sb, str_bytes cs) w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q OK X KR VIS RF G2 G1 Hr2 Hr);
      [unfold IT_STACK, AINTRIN_STACK; lia | reflexivity | | exact Hknn | exact Hfk |].
    - destruct PRE as (_ & P2). split; [exact G10 | exact P2].
    - intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 KEPT MU WM (r & Rr & Er).
      exact (K msF1 mo1 m1 R1 r KR1 VIS1 RF1 X1 KEPT MU WM Rr Er).
  Qed.
End Imp.
