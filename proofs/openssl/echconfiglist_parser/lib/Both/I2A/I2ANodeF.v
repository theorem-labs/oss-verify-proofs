(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit I2ANodeM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

Section NodeF.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Local Abbreviation IM := (im_ro IMX).
  Local Abbreviation RO := (ro_of (ka_K A)).
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HIMX : image_ok asegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Hypothesis Hpfc : Forall (fun e : int * list int => trace_ok (as_TR H) (to_Z (fst e)) (map to_Z (snd e))) (ka_pfc A).
  Let HH : asan_rt_hyps H := proj1 HHx.

  Hypothesis HROC : ro_const A.

  Ltac hk_err :=
    let E1 := fresh "Eerr" in let E2 := fresh "Eerr8" in let E3 := fresh "Ebi" in let E4 := fresh "Ewin" in let E5 := fresh "Eac" in
    let E6 := fresh "Etp" in let E7 := fresh "Em1" in let E8 := fresh "Em2" in let E9 := fresh "Em3" in let E10 := fresh "Em4" in
    let E11 := fresh "Ef1" in let E12 := fresh "Ef2" in let E13 := fresh "Ef3" in let E14 := fresh "Ef4" in
    let E15 := fresh "Est16" in let E16 := fresh "Est40" in
    destruct (HK_err A HK) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16);
    pose proof (i63_range (c_errbi K)); pose proof (i63_range (c_errcell K)); pose proof (i63_range (c_stack K));
    pose proof (i63_range (c_mstack K)).
  Ltac hk_xw c Hc :=
    let X := fresh "Xw" in
    pose proof (xw_cell_ok_spec c (HK_xw A HK c Hc)) as X;
    destruct X as (? & ? & ? & ? & ? & ?); pose proof (i63_range c).


  Theorem anode_free_sound : forall Q st st' rho msF mo,
    anode_free A st = Some st' ->
    to_Z (f_pc (a_F st)) = AFREE_STUB ->
    cells0_in A (f_mem (a_F st)) ->
    I2RA H IMX A Q st rho msF mo ->
    as_SR H (fun c' => exists rho', I2RA H IMX A Q st' rho' (cfg_ms c') (cfg_model c')) (mkCfg msF mo).
  Proof.
    intros Q st st' rho msF mo Hnode Hpc Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_free in Hnode.
    destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (base_tag (FxState.rget (a_F st) 10)) as [tb|] eqn:Ha0; [|discriminate].
    destruct (bsize_of tb (a_blk st)) as [n|] eqn:Hbs; [|discriminate].
    destruct (iget tb (f_mem (a_F st))) as [rgb|] eqn:Hrgb; [|discriminate].
    destruct (iget (tb + 1)%uint63 (f_mem (a_F st))) as [rgs|] eqn:Hrgs; [|discriminate].
    destruct (pop_cost 1 n 0 (a_cs st)) as [cs|] eqn:Hpop; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hguard; [|discriminate] end.
    cbv zeta in Hnode.
    destruct (drop_stack off (iremove (tb + 1)%uint63 (iremove tb (f_mem (a_F st))))) as [M1|] eqn:HM1; [|discriminate].
    destruct (set_errno K (a_n st + 15)%uint63 M1) as [M2|] eqn:HM2; [|discriminate].
    injection Hnode as <-.
    destruct (call_okn_inv _ _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv _ _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv.
    destruct (base_tag_inv _ _ Ha0) as [Ea0 Htb0].
    pose proof (pop_cost_inv _ _ _ _ _ Hpop) as Ecs.
    rewrite !andb_true_iff in Hguard. destruct Hguard as [[[[Hnc Hk1] Htb4] Hchain] Hrook].
    apply Uint63.leb_spec in Hnc. apply Uint63.leb_spec in Hk1. apply Uint63.leb_spec in Htb4.
    change (to_Z 1%uint63) with 1 in Hk1. change (to_Z 4%uint63) with 4 in Htb4.
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    rewrite !iget_iremove in Hrg1.
    destruct (1 =? tb + 1)%uint63 eqn:E1s; [discriminate|]. destruct (1 =? tb)%uint63 eqn:E1b; [discriminate|].
    destruct (set_errno_inv _ _ _ _ HM2) as (rg0 & pe & Hrg0' & Hpe & Hpew & ->).
    rewrite !iget_iset, !iget_iremove in Hrg0'. change ((0 =? 1)%uint63) with false in Hrg0'.
    destruct (0 =? tb + 1)%uint63 eqn:E0s; [discriminate|]. destruct (0 =? tb)%uint63 eqn:E0b; [discriminate|]. cbv iota in Hrg0'.
    rename Hrg0' into Hrg0M.
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (t := a_n st) in *.
    assert (Hag : agree t rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR.
    pose proof (canonR_R asegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    replace (f_pc F) with (f_pc (a_F st)) in Ems by reflexivity. rewrite Hpc in Ems.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 ATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    (* [comment removed for export] *)
    pose proof Hbs as Hbs'. rewrite XG in Hbs'. destruct (bsize_of_map _ _ _ Hbs') as (gb & Hgb & Hgbt & Hgbs). subst n.
    pose proof (proj1 (Forall_forall _ _) XGin gb Hgb) as (Hgbin & Hgbrho & Hgbsz & Hgbtg1 & Hgbtg2 & (rgb_ & Hgbrg & Hgblo & Hgblen & Hgbk & _) & Hgbsh).
    rewrite Hgbt in Hgbrg. fold F in Hrgb. rewrite Hrgb in Hgbrg. injection Hgbrg as <-.
    rewrite Hgbt in Hgbsh. fold F in Hrgs. destruct (Hgbsh rgs Hrgs) as (Ergs & Hgbrs & Hgbad).
    pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hgb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    assert (Htblt : 4 <= to_Z tb /\ to_Z tb + 1 < to_Z t) by (rewrite <- Hgbt; split; assumption).
    pose proof Hn59 as Hn59'. change (to_Z two59) with (2 ^ 59) in Hn59'.
    assert (Ea0v : rv rho F 10 = Z_to_bv 64 (g_addr gb)).
    { rewrite Erv. change (of_Z 10) with 10%uint63. fold F in Ea0. rewrite Ea0. change (W64 0 0) with w_zero.
      rewrite dv_tag_zero by slia. rewrite <- Hgbt, Hgbrho. reflexivity. }
    (* [comment removed for export] *)
    destruct (rw_c4_of_stk asegs _ _ Xerr) as [errv Herrv].
    assert (EerrA : bv_unsigned (rv rho F 4) + -164 = errA A).
    { rewrite Etpv. unfold errA. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      unfold ATP. rewrite Z.mod_small by slia. unfold AERRNO, ATP in Eerr. slia. }
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q) Xstk ltac:(rewrite Espu; slia)) as [Hstk_lo Hstk_hi].
    (* [comment removed for export] *)
    pose proof (i63_range (a_cost st)). pose proof (i63_range (c_cost K)). pose proof (i63_range (g_size gb)).
    pose proof (i63_range (a_cnt st)). pose proof (i63_range (c_cnt K)). destruct (HK_caps A HK) as (Hcap1 & Hcap2 & Hcap3).
    assert (Ecost' : to_Z (a_cost st - g_size gb)%uint63 = to_Z (a_cost st) - to_Z (g_size gb)).
    { rewrite Uint63.sub_spec. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    assert (Ecnt' : to_Z (a_cnt st - 1)%uint63 = to_Z (a_cnt st) - 1).
    { rewrite Uint63.sub_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    (* [comment removed for export] *)
    destruct XAL as (done & Ecsq & HAL).
    assert (HCf : as_Cf H (to_Z (g_size gb)) <= as_AL H s /\ as_AL H s - as_Cf H (to_Z (g_size gb)) >= q_AL0 Q - csum H (done ++ [(1%uint63, g_size gb, 0%uint63)])).
    { rewrite Ecs in Ecsq. pose proof XAL0 as B0. rewrite Ecsq, csum_app in B0. cbn [csum fold_right] in B0. fold (csum H cs) in B0.
      unfold cost1 in B0. change ((1 =? 0)%uint63) with false in B0. change ((1 =? 1)%uint63) with true in B0. cbv iota in B0.
      pose proof (csum_nonneg H HHx cs). rewrite csum_app. cbn [csum fold_right]. unfold cost1. change ((1 =? 0)%uint63) with false. change ((1 =? 1)%uint63) with true. cbv iota. slia. }
    destruct HCf as [HCf HAL'].
    (* [comment removed for export] *)
    destruct (stk_carve asegs (ms_mem ms) (g_addr gb) (g_addr gb + to_Z (g_size gb)) (Z.to_nat (to_Z (g_size gb))) (proj1 (Forall_forall _ _) XGstk gb Hgb) ltac:(slia)) as [_ (bs & Hbs0)].
    rewrite Z2Nat.id in Hbs0 by slia. replace (g_addr gb + to_Z (g_size gb) - to_Z (g_size gb)) with (g_addr gb) in Hbs0 by slia.
    pose proof Hgbad as [_ SHgb].
    (* [comment removed for export] *)
    pose proof (ah_nodup H HH _ _ _ Xheap) as HndLB.
    destruct (lb_remove_facts H (ah_lb_remove H HH) LB (g_id gb) (g_addr gb) (to_Z (g_size gb)) HndLB Hgbin) as (Lby & Llen & Lin & Lin' & Lnotp).
    set (LBr := as_lb_remove H (g_id gb) LB) in *.
    (* [comment removed for export] *)
    destruct (chain_okb_trace H IMX A HK HHx Hpfc _ _ _ _ _ _ _ _ _ _ _ _ _ X Hchain) as (CH & Hch & Htr).
    assert (Hpc0 : to_Z (ka_pc0f A) = APC0_FREE).
    { destruct (HK_parts A HK) as (_ & _ & Hpcs & _). unfold K_pcs_ok in Hpcs. rewrite !andb_true_iff in Hpcs.
      destruct Hpcs as [[[_ _] Hf] _]. apply Z.eqb_eq in Hf. exact Hf. }
    rewrite Hpc0 in Htr.
    assert (Hral : bv_unsigned (rv rho F 1) = to_Z l).
    { rewrite Erav, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). pose proof (i63_range l). apply Z.mod_small. slia. }
    rewrite <- Hral in Htr.
    assert (Hch8 : as_chain H (ms_mem ms) (bv_unsigned (rv rho F 8)) CH) by exact Hch.
    (* [comment removed for export] *)
    eapply (ah_mono H HH).
    { eapply ((ah_free H HH) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q_F Q) (q_fc Q) msF (ms_mem ms) s LB (g_id gb) (g_addr gb) (to_Z (g_size gb)) (q_lo Q) (q_B Q) errv mo CH bs (shadow_of (to_Z (g_size gb)))).
      - rewrite <- Ems. exact Xvis.
      - exact Xheap.
      - exact Xak.
      - exact Hgbin.
      - exact HCf.
      - exact Hbs0.
      - exact SHgb.
      - rewrite shadow_of_length by slia. reflexivity.
      - exact Xaux.
      - rewrite Espu. slia.
      - exact Hstk_lo.
      - slia.
      - rewrite Espu. unfold AFREE_STACK in *. slia.
      - rewrite EerrA. exact Herrv.
      - exact Xinv.
      - exact Etpv.
      - rewrite Espu. clear - Hoff16 Hsp32 Hsp16 Hcs Hoff Est16. Z.div_mod_to_equations. slia.
      - exact Xac.
      - exact Hch8.
      - exact Htr.
      - exact Ea0v. }
    (* [comment removed for export] *)
    intros [msF' mo'] Hpost. unfold free_post in Hpost. cbn [cfg_ms cfg_model] in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & s'
                       & Evis' & Hak' & Hmpres' & Hinv' & Hstk' & Herr' & Haux' & Hpres & Hheap' & Hac' & HALs').
    cbn [cfg_ms cfg_model]. fold LBr in Hpres, Hheap'.
    set (L16 := [t0'; t1'; t2'; a0'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6'; errv]).
    set (rho' := rho_ext rho t L16).
    exists rho'.
    pose proof (i63_range t) as Ht.
    change (to_Z two59) with (2 ^ 59) in Hn59.
    assert (Hag' : agree t rho rho') by (apply agree_ext; [slia | slia | exact Xr0]).
    assert (Et16 : to_Z (t + 16)%uint63 = to_Z t + 16) by (rewrite to_Z_add_small; change (to_Z 16%uint63) with 16; slia).
    assert (Et15 : to_Z (t + 15)%uint63 = to_Z t + 15) by (rewrite to_Z_add_small; change (to_Z 15%uint63) with 15; slia).
    assert (EL16 : forall x (k : nat), (k < 16)%nat -> to_Z x = to_Z t + Z.of_nat k -> rho' x = nth k L16 w0).
    { intros x k Hk Hx. subst rho'. apply (rho_ext_at rho t L16 x k); [subst L16; cbn; slia | exact Hx]. }
    assert (Erho'e : rho' (t + 15)%uint63 = errv) by (rewrite (EL16 _ 15%nat); [reflexivity | slia | rewrite Et15; slia]).
    destruct Xnamed as [XG0in XLB0nd].
    (* [comment removed for export] *)
    assert (Hgbid : forall b, In b (q_LB0 Q) -> ~ In (blk_id b) (map g_id (q_G0 Q)) -> blk_id b <> g_id gb).
    { intros b Hb Hni E. destruct (proj1 (Forall_forall _ _) XGnew gb Hgb) as [Hgb0 | [_ [Hgbids _]]].
      - apply Hni. rewrite E. apply in_map. exact Hgb0.
      - exact (Hgbids b Hb Hni (eq_sym E)). }
    assert (Hclient : forall a, 0 <= a < 2 ^ 64 -> client0 H Q a -> ~ named_addr Q a -> aclient_range H LBr (bv_unsigned (rv rho F 2)) a 1).
    { intros a Ha Hcl Hna. rewrite Espu.
      unfold client0, aclient_addr in Hcl. destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
      - left. slia.
      - right. left. intros a' Ha'. replace a' with a by slia. exact Hst.
      - destruct (in_dec bptr_eq_dec (blk_id b) (map g_id (q_G0 Q))) as [Hi|Hni].
        + exfalso. apply Hna. apply in_map_iff in Hi as (g0 & Eg & Hg0).
          pose proof (proj1 (Forall_forall _ _) XG0in g0 Hg0) as Hg0in.
          pose proof (nodup_ids_eq _ b _ XLB0nd Hb Hg0in ltac:(rewrite <- Eg; reflexivity)) as ->.
          exists g0. split; [exact Hg0|]. left. cbn [blk_addr blk_size fst snd] in Hr. exact Hr.
        + right. right. left. exists b. split; [apply Lin; [exact (XLB0 b Hb Hni) | exact (Hgbid b Hb Hni)]|]. slia.
      - destruct (in_dec bptr_eq_dec (blk_id b) (map g_id (q_G0 Q))) as [Hi|Hni].
        + exfalso. apply Hna. apply in_map_iff in Hi as (g0 & Eg & Hg0).
          pose proof (proj1 (Forall_forall _ _) XG0in g0 Hg0) as Hg0in.
          pose proof (nodup_ids_eq _ b _ XLB0nd Hb Hg0in ltac:(rewrite <- Eg; reflexivity)) as ->.
          exists g0. split; [exact Hg0|]. right. cbn [blk_addr blk_size fst snd] in Hr. exact Hr.
        + right. right. right. left. exists b. split; [apply Lin; [exact (XLB0 b Hb Hni) | exact (Hgbid b Hb Hni)]|]. slia.
      - do 4 right. left. slia.
      - do 5 right. left. slia.
      - do 6 right. slia. }
    assert (Hclient_addr : forall a, 0 <= a < 2 ^ 64 -> client0 H Q a -> ~ named_addr Q a -> aclient_addr H LBr (bv_unsigned (rv rho F 2)) a).
    { intros a Ha Hcl Hna. eapply aclient_range_addr; [exact (Hclient a Ha Hcl Hna) | slia]. }
    pose proof (ah_nodup H HH _ _ _ Hheap') as HndLB'.
    (* [comment removed for export] *)
    assert (NDg : forall g1 g2, In g1 G -> In g2 G -> g_id g1 = g_id g2 -> g1 = g2).
    { clear -XGnd. induction G as [|x G' IH]; intros g1 g2 H1 H2 E; [destruct H1|]. cbn [map] in XGnd.
      pose proof (proj1 (NoDup_cons_iff _ _) XGnd) as [Hn Hnd2].
      destruct H1 as [<-|H1]; destruct H2 as [<-|H2]; [reflexivity | | | exact (IH Hnd2 g1 g2 H1 H2 E)].
      - exfalso. apply Hn. rewrite E. apply in_map. exact H2.
      - exfalso. apply Hn. rewrite <- E. apply in_map. exact H1. }
    assert (Htags : forall g, In g G -> g <> gb -> g_tag g <> tb /\ g_tag g <> (tb + 1)%uint63 /\ (g_tag g + 1)%uint63 <> tb /\ (g_tag g + 1)%uint63 <> (tb + 1)%uint63).
    { intros g Hg Hne. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & Hgtg1 & Hgtg2 & (rgg & Hgg & _ & _ & Hkg & _) & Hshg). destruct Xn0 as [_ Hn60].
      assert (T1 : g_tag g <> tb).
      { intros E. apply Hne. clear - XGtnd Hg Hgb E Hgbt.
        induction G as [|x G' IH]; [destruct Hg|]. cbn [map] in XGtnd. pose proof (proj1 (NoDup_cons_iff _ _) XGtnd) as [Hn Hnd2].
        destruct Hg as [<-|Hg]; destruct Hgb as [<-|Hgb]; [reflexivity | | | exact (IH Hnd2 Hgb Hg)].
        - exfalso. apply Hn. rewrite E, <- Hgbt. apply in_map. exact Hgb.
        - exfalso. apply Hn. rewrite Hgbt, <- E. apply in_map. exact Hg. }
      split; [exact T1|]. split.
      - intros E. rewrite E in Hgg. fold F in Hgg. rewrite Hrgs in Hgg. injection Hgg as ->. rewrite Ergs in Hkg. unfold sh_region in Hkg. cbn [rg_kind] in Hkg. discriminate Hkg.
      - split.
        + intros E. specialize (Hshg rgb ltac:(rewrite E; exact Hrgb)). destruct Hshg as (Erb & _). rewrite Erb in Hgbk. unfold sh_region in Hgbk. cbn [rg_kind] in Hgbk. discriminate Hgbk.
        + intros E. apply T1. apply to_Z_inj. apply (f_equal to_Z) in E. pose proof (i63_range (g_tag g)). pose proof (i63_range tb).
          rewrite !to_Z_add_small in E by (change (to_Z 1%uint63) with 1; clear - Hgtg2 Htblt Hn60 H H0; slia). clear - E; slia. }
    assert (HGids : forall g, In g (gremove tb G) -> In (g_id g) (map blk_id LBr)).
    { intros g Hg. apply In_gremove in Hg as [Hg Hgt]. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _).
      replace (g_id g) with (blk_id (g_id g, g_addr g, to_Z (g_size g))) by reflexivity. apply in_map. apply Lin; [exact Hin|].
      cbn [blk_id fst]. intros E. apply Hgt. rewrite <- Hgbt. f_equal. exact (NDg _ _ Hg Hgb E). }
    (* [comment removed for export] *)
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> aclient_addr H LBr (bv_unsigned (rv rho F 2)) a ->
                     rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a)
                     /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hc. destruct (Hpres a Ha Hc) as [E W]. split; [apply rview_eq_of_mem; exact E | exact W]. }
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) a0'
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    exists s', LBr, (gremove tb G), FF, XS, ms1.
    assert (HRn' : Rn asegs IM (t + 16)%uint63 rho'
              (FS (ret_of l) (clobber clob15 t (f_regs F))
                  (iset 0 (err_region K (t + 15) rg0 pe) (iset 1 (drop_below off rg1) (iremove (tb + 1)%uint63 (iremove tb (f_mem F))))) None)
              ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree t rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Et16; slia]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z t + 16 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Et16; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''old : forall x, to_Z x < to_Z t -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by slia. subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; slia); exact Xr1).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) a0'
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; a0';
                      a1'; a2'; a3'; a4'; a5'; a6'; a7'; rv rho F 18; rv rho F 19; rv rho F 20; rv rho F 21; rv rho F 22; rv rho F 23;
                      rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; t3'; t4'; t5'; t6']).
        apply R_regs_of_match; [exact Hrho''0 | reflexivity |].
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 5) (rv rho F 6) (rv rho F 7) (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     (rv rho F 11) (rv rho F 12) (rv rho F 13) (rv rho F 14) (rv rho F 15) (rv rho F 16) (rv rho F 17) (rv rho F 18) (rv rho F 19) (rv rho F 20)
                     (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) (rv rho F 28) (rv rho F 29) (rv rho F 30) (rv rho F 31))
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; rv rho F 5; rv rho F 6; rv rho F 7; rv rho F 8; rv rho F 9; rv rho F 10;
                      rv rho F 11; rv rho F 12; rv rho F 13; rv rho F 14; rv rho F 15; rv rho F 16; rv rho F 17; rv rho F 18; rv rho F 19; rv rho F 20;
                      rv rho F 21; rv rho F 22; rv rho F 23; rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; rv rho F 28; rv rho F 29; rv rho F 30; rv rho F 31]) in HR''.
        pose proof (regs_match_of_R _ _ _ _ _ _ _ _ _ _ _ HR'') as Hpre.
        assert (Hnd15 : List.NoDup clob15) by (apply nodupb_spec; reflexivity).
        assert (Hcl : forall k : int, iget k (clobber clob15 t (f_regs F)) =
                      match index_of k clob15 with
                      | Some i => Some (FV (of_Z (to_Z t + Z.of_nat i)) w_zero)
                      | None => iget k (f_regs F) end).
        { intros k. apply iget_clobber; [exact Hnd15 | cbn [length clob15]; slia]. }
        apply regs_match_intro. cbn [seq].
        repeat (apply Forall_cons || apply Forall_nil);
          cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ];
          match goal with |- _ = dv _ (FxState.rget ?FF ?k) =>
            let kk := eval vm_compute in k in change k with kk; rewrite (rget_regs' FF kk eq_refl) end;
          cbn [f_regs].
        all: try (rewrite Hcl;
                  match goal with |- _ = dv _ match match ?ix with _ => _ end with _ => _ end =>
                    let ii := eval vm_compute in ix in change ix with ii end; cbv iota).
        all: first
          [ (* [comment removed for export] *)
            match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); slia);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia);
              rewrite (EL16 (of_Z (to_Z t1 + Z.of_nat i)) i); [reflexivity | slia | rewrite Etag; slia]
            end
          | (* [comment removed for export] *)
            match goal with |- rv _ _ ?kz = dv _ match iget ?ki (f_regs ?FF) with _ => _ end =>
              rewrite <- (rget_regs' FF ki eq_refl);
              let kn := eval vm_compute in (Z.to_nat kz) in
              let HP := fresh "HP" in
              pose proof (Hpre kn ltac:(slia)) as HP; cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in HP; exact HP
            end
          ].
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        cbn [f_mem ms_mem].
        destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0_. rewrite Hrg0M in Hrg0_. injection Hrg0_ as <-.
        destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
        apply mem_ok_parts.
        + intros t' rg' Ht'. rewrite !iget_iset, !iget_iremove in Ht'.
          destruct (t' =? 0)%uint63 eqn:E0.
          * (* [comment removed for export] *) apply Uint63.eqb_spec in E0. subst t'. injection Ht' as <-.
            eapply (region0_part asegs IM rho'' Hrho''0 IMX eq_refl HIMX HWRX K (ms_mem ms) m' rg0 pe (t + 15)%uint63 errv
                      (fun c => 0 <= c /\ c + 8 <= AIMG_TOP /\ ((exists x, In x (c_xw K) /\ to_Z x = c)
                                                           \/ (exists cc, In (of_Z c, cc) (c_ro K) /\ aconst_pin_b (of_Z c) cc = false)))).
            -- exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0M).
            -- exact Hd0.
            -- exact Hpg0.
            -- intros pn p0 ci c Hp0 Hc. pose proof (i63_range pn) as Rpn. pose proof (i63_range ci) as Rci.
               destruct (Xinb 0%uint63 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hcb [Hci512 _]]. rewrite Hlen0 in Hcb.
               destruct (Hc0 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hx | [He | (cc & Hcc)]].
               ** left. split; [slia|]. split; [clear -Hcb; unfold AIMG_TOP in *; slia|]. left; exact Hx.
               ** right; left; exact He.
               ** destruct (aconst_pin_b (of_Z (to_Z pn * 4096 + to_Z ci * 8)) cc) eqn:Epin.
                  --- (* [comment removed for export] *)
                      right; right. destruct (aconst_pin_sound m' _ cc Hac' Epin) as (sl & -> & Hsl).
                      assert (Ea : to_Z (of_Z (to_Z pn * 4096 + to_Z ci * 8)) = to_Z pn * 4096 + to_Z ci * 8)
                        by (apply toZ_of_Z_small; clear -Hcb Rpn Rci; unfold AIMG_TOP in *; slia).
                      pose proof (ro_okb_sound K (f_mem F) rg0 _ (CB sl) pn p0 ci c Hrook Hrg0M Hcc Hp0 Hc (eq_sym Ea) ltac:(clear -Hci512 Rci; slia)) as ->.
                      exists sl. split; [reflexivity|]. intros j Hj. pose proof (Hsl rho'' j Hj) as T. rewrite Ea in T. exact T.
                  --- left. split; [slia|]. split; [clear -Hcb; unfold AIMG_TOP in *; slia|]. right. exists cc. split; [exact Hcc | exact Epin].
            -- intros c a (Hc0' & Hc8 & [(x & Hx & <-) | (cc & Hcc & Hnp)]) Ha.
               ++ clear - Hkeep Hx Ha Hc0' Hc8 HK Espu Hoff Hcs Hlsp Hhl ACEILB. hk_xw x Hx.
                  apply (proj1 (Hkeep a ltac:(unfold AIMG_TOP in *; slia) ltac:(right; left; eapply aimg8_b_spec; [|exact Ha]; unfold aimg8_b; unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in *;
                           rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le; slia))).
               ++ destruct (aimg8_b c) eqn:E8.
                  ** apply (proj1 (Hkeep a ltac:(unfold AIMG_TOP in *; slia) ltac:(right; left; exact (aimg8_b_spec _ _ E8 Ha)))).
                  ** pose proof (HROC _ _ Xac Hac' Xinv Hinv' (of_Z c) cc Hcc) as E. rewrite toZ_of_Z_small in E by (unfold AIMG_TOP in *; slia).
                     specialize (E E8 Hnp (a - c) ltac:(slia)). replace (c + (a - c)) with a in E by slia. exact E.
            -- exact Hpe.
            -- exact Hinv'.
            -- rewrite EerrA in Herr'. exact Herr'.
            -- rewrite dv_tag_zero by (rewrite Et15; slia). rewrite Erho'' by (rewrite Et15; slia). exact Erho'e.
            -- exact Eerr8.
            -- exact Ebi.
            -- destruct (err_page_ok_inv _ _ Hep) as (rg0b & pb & Hrg0b & Hir & _). fold F in Hrg0b. rewrite Hrg0M in Hrg0b. injection Hrg0b as <-.
               unfold in_region in Hir. rewrite !andb_true_iff in Hir. destruct Hir as [[[Hob _] _] Hir]. apply Uint63.leb_spec in Hir.
               apply Uint63.ltb_spec in Hob. change (to_Z off_bound) with (2 ^ 62) in Hob.
               rewrite Uint63.add_spec in Hir. change (to_Z 8%uint63) with 8 in Hir. change wB with (2 ^ 63) in Hir.
               pose proof (i63_range (c_errcell K)). pose proof (i63_range (rg_len rg0)). rewrite Z.mod_small in Hir by slia. exact Hir.
            -- rewrite Hlen0. reflexivity.
          * destruct (t' =? 1)%uint63 eqn:E1.
            -- (* [comment removed for export] *) apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
               destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
               apply (stack_part asegs IM rho'' (ms_mem ms) m' rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q)).
               ++ exact Erho''1.
               ++ exact Hlo1.
               ++ exact Hd1.
               ++ exact Hkd1.
               ++ rewrite Hlen1. reflexivity.
               ++ rewrite Hlen1. slia.
               ++ clear - Hoff16 Hoff. Z.div_mod_to_equations. slia.
               ++ exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1).
               ++ exact Xstk.
               ++ slia.
               ++ rewrite <- Espu. exact Hstk'.
               ++ intros a Ha. destruct Xstk as (_ & H64 & _). apply Hkeep; [slia | left; rewrite Espu; slia].
            -- (* [comment removed for export] *)
               destruct (t' =? tb + 1)%uint63 eqn:Ets; [discriminate|]. destruct (t' =? tb)%uint63 eqn:Etb; [discriminate|].
               assert (Hne0 : t' <> 0%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E0; discriminate).
               assert (Hne1 : t' <> 1%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E1; discriminate).
               apply (old_parts H IMX A HK HHx HSH0 _ _ _ _ _ _ _ _ _ _ _ rho'' m' LBr (bv_unsigned (rv rho F 2)) [tb] t' rg' X).
               ++ intros x Hx. apply Erho''old. exact Hx.
               ++ exact Hkeep.
               ++ rewrite Espu. slia.
               ++ intros g Hg Hni. apply Lin; [exact (proj1 (proj1 (Forall_forall _ _) XGin g Hg))|]. cbn [blk_id fst].
                  intros E. apply Hni. left. rewrite <- Hgbt. f_equal. symmetry. exact (NDg _ _ Hg Hgb E).
               ++ exact Lin'.
               ++ exact Hac'.
               ++ exact Hinv'.
               ++ exact Ht'.
               ++ exact Hne0.
               ++ exact Hne1.
               ++ intros g Hg [E|[]]. subst tb. split; intros E'; subst t'.
                  ** rewrite E, Uint63.eqb_refl in Etb. discriminate.
                  ** rewrite E, Uint63.eqb_refl in Ets. discriminate.
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2. rewrite !iget_iset, !iget_iremove in Hi1, Hi2.
          assert (Hold : forall t' rg',
                    (if (t' =? 0)%uint63 then Some (err_region K (t + 15) rg0 pe)
                     else if (t' =? 1)%uint63 then Some (drop_below off rg1)
                     else if (t' =? tb + 1)%uint63 then None else if (t' =? tb)%uint63 then None else iget t' (f_mem F)) = Some rg' ->
                    exists rg, iget t' (f_mem F) = Some rg /\ rg_lo rg = rg_lo rg' /\ rg_len rg = rg_len rg').
          { intros t' rg' Ht'.
            destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; subst t'; injection Ht' as <-; exists rg0; split; [exact Hrg0M | split; reflexivity]|].
            destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; subst t'; injection Ht' as <-; exists rg1; split; [exact Hrg1 | split; reflexivity]|].
            destruct (t' =? tb + 1)%uint63; [discriminate|]. destruct (t' =? tb)%uint63; [discriminate|].
            exists rg'. split; [exact Ht' | split; reflexivity]. }
          destruct (Hold t1 r1 Hi1) as (q1 & Hq1 & El1 & En1). destruct (Hold t2 r2 Hi2) as (q2 & Hq2 & El2 & En2).
          rewrite <- El1, <- En1, <- El2, <- En2. exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) XGin gb Hgb) as (_ & _ & _ & _ & Hgbtg2' & _).
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mkc f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS ms1].
    - exact Evis'.
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr2 | change (to_Z 2%uint63) with 2; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr3 | change (to_Z 3%uint63) with 3; slia].
    - eapply agree_trans; [exact Xag | exact Hag' | slia].
    - rewrite Et16. slia.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmpres').
    - exact Hheap'.
    - eapply (RFS_via_apres H HH); [exact Xrfs | exact Hpres].
    - exact Hac'.
    - (* [comment removed for export] *) destruct Xst0 as (g & G1' & G2' & G3' & AD). exists g. split; [exact G1'|]. split; [exact G2'|]. split; [exact G3'|].
      destruct AD as [ADn SH]. split; [exact ADn|]. eapply (apres_SHAD H); [exact Hpres | exact SH |].
      do 6 right. rewrite shadow_of_length by slia. pose proof (SHAD_aligned _ _ _ SH) as [_ G8].
      assert (M1 : sh aceil <= sh g) by (apply sh_mono; slia).
      assert (M2 : sh g + nsh (q_shi Q - g) <= AHI_LO).
      { clear - G1' G2' G8. unfold nsh, sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia. }
      slia.
    - eapply (chain_via_apres H HH); [exact Xch | exact Hpres |]. intros fp ra Hin. rewrite Espu. specialize (XCH0 fp ra Hin). slia.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - (* [comment removed for export] *) exists (done ++ [(1%uint63, g_size gb, 0%uint63)]). split; [rewrite Ecsq, Ecs, <- app_assoc; reflexivity | slia].
    - exact XAL0.
    - (* [comment removed for export] *) cbn [map]. rewrite XG. apply bremove_map. exact XGtnd.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. apply In_gremove in Hg as [Hg Hgt].
      assert (Hne : g <> gb) by (intros ->; exact (Hgt Hgbt)).
      destruct (Htags g Hg Hne) as (T1 & T2 & T3 & T4).
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hsh).
      pose proof (i63_range (g_tag g)). destruct Xn0 as [Hn4 Hn60].
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      split; [apply Lin; [exact Hin | cbn [blk_id fst]; intros E; apply Hne; exact (NDg _ _ Hg Hgb E)]|].
      split; [subst rho'; rewrite rho_ext_old by slia; exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
      split; [rewrite Et16; slia|]. split.
      + exists rgg. rewrite !iget_iset, !iget_iremove.
        destruct (g_tag g =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); change (to_Z 0%uint63) with 0 in *; slia|].
        destruct (g_tag g =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); change (to_Z 1%uint63) with 1 in *; slia|].
        rewrite (proj2 (Uint63.eqb_false_spec _ _) T2), (proj2 (Uint63.eqb_false_spec _ _) T1).
        split; [exact Hgg|]. repeat split; assumption.
      + intros rg' Hrg'. rewrite !iget_iset, !iget_iremove in Hrg'.
        destruct (g_tag g + 1 =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); rewrite Etg1 in *; change (to_Z 0%uint63) with 0 in *; slia|].
        destruct (g_tag g + 1 =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); rewrite Etg1 in *; change (to_Z 1%uint63) with 1 in *; slia|].
        rewrite (proj2 (Uint63.eqb_false_spec _ _) T4), (proj2 (Uint63.eqb_false_spec _ _) T3) in Hrg'.
        destruct (Hsh rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia); exact Hrs|].
        eapply (apres_addressable H); [exact Hpres | exact Had' |]. apply Lin; [exact Hin | cbn [blk_id fst]; intros E; apply Hne; exact (NDg _ _ Hg Hgb E)].
    - (* [comment removed for export] *) unfold gremove. clear - XGnd. induction G as [|x G' IH]; cbn [List.filter map]; [constructor|].
      cbn [map] in XGnd. pose proof (proj1 (NoDup_cons_iff _ _) XGnd) as [Hn Hnd2].
      destruct (negb (g_tag x =? tb)%uint63); [|exact (IH Hnd2)]. cbn [map]. constructor; [|exact (IH Hnd2)].
      intros Hin. apply Hn. apply in_map_iff in Hin as (g' & E & Hg'). apply filter_In in Hg' as [Hg' _]. rewrite <- E. apply in_map. exact Hg'.
    - (* [comment removed for export] *) unfold gremove. clear - XGtnd. induction G as [|x G' IH]; cbn [List.filter map]; [constructor|].
      cbn [map] in XGtnd. pose proof (proj1 (NoDup_cons_iff _ _) XGtnd) as [Hn Hnd2].
      destruct (negb (g_tag x =? tb)%uint63); [|exact (IH Hnd2)]. cbn [map]. constructor; [|exact (IH Hnd2)].
      intros Hin. apply Hn. apply in_map_iff in Hin as (g' & E & Hg'). apply filter_In in Hg' as [Hg' _]. rewrite <- E. apply in_map. exact Hg'.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. apply In_gremove in Hg as [Hg _]. exact (proj1 (Forall_forall _ _) XGnew g Hg).
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. apply In_gremove in Hg as [Hg Hgt].
      assert (Hne : g <> gb) by (intros ->; exact (Hgt Hgbt)).
      pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _ & Hsz & _).
      apply (stk_pres asegs (ms_mem ms)); [exact Hs|]. intros a Ha. apply Hpres; [pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _); slia|].
      unfold aclient_addr. do 2 right. left. exists (g_id g, g_addr g, to_Z (g_size g)).
      split; [apply Lin; [exact Hin | cbn [blk_id fst]; intros E; apply Hne; exact (NDg _ _ Hg Hgb E)] | cbn [blk_addr blk_size fst snd]; slia].
    - exact XFF.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkf & Half & Hdff) & (rgs' & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)). pose proof (i63_range tb).
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
      assert (Etb1 : to_Z (tb + 1)%uint63 = to_Z tb + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      split; [subst rho'; rewrite rho_ext_old by slia; exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia); exact Hf1|].
      split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; slia); exact Hf2|]. split; [exact Hk|]. split; [exact Htg1|]. split; [rewrite Et16; slia|].
      destruct XTsep as (_ & S2 & _). pose proof (S2 gb f Hgb Hf) as Sgf. rewrite Hgbt in Sgf.
      assert (NT : forall x, (to_Z x = to_Z (f_tag f) \/ to_Z x = to_Z (f_tag f) + 1 \/ to_Z x = to_Z (f_tag f) + 2) ->
                   (x =? 0)%uint63 = false /\ (x =? 1)%uint63 = false /\ (x =? tb + 1)%uint63 = false /\ (x =? tb)%uint63 = false).
      { intros x Hx. repeat split;
          (destruct (Uint63.eqb x _) eqn:E; [|reflexivity]; apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; rewrite ?Etb1 in E;
           change (to_Z 0%uint63) with 0 in E; change (to_Z 1%uint63) with 1 in E; exfalso; clear - Hx E Sgf Htg1; slia). }
      destruct (NT (f_tag f) ltac:(left; reflexivity)) as (N0 & N1 & N2 & N3).
      destruct (NT (f_tag f + 1)%uint63 ltac:(right; left; exact Etg1)) as (M0 & M1' & M2' & M3).
      destruct (NT (f_tag f + 2)%uint63 ltac:(right; right; exact Etg2)) as (P0 & P1 & P2 & P3).
      split; [exists rgf; rewrite !iget_iset, !iget_iremove, N0, N1, N2, N3; split; [exact Hgf|]; repeat split; assumption|].
      split; [exists rgs'; rewrite !iget_iset, !iget_iremove, M0, M1', M2', M3; split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite !iget_iset, !iget_iremove, P0, P1, P2, P3; exact Hflg|].
      repeat split; assumption.
    - exact XFFnd.
    - exact XFFtnd.
    - (* [comment removed for export] *) destruct XTsep as (S1 & S2 & S3). split; [|split; [|exact S3]].
      + intros g g' Hg Hg' Hne. apply In_gremove in Hg as [Hg _]. apply In_gremove in Hg' as [Hg' _]. exact (S1 g g' Hg Hg' Hne).
      + intros g f Hg Hf. apply In_gremove in Hg as [Hg _]. exact (S2 g f Hg Hf).
    - exact XFFlen.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite !iget_iset, !iget_iremove in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; left; exact E0|].
      destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; right; left; exact E1|].
      destruct (t' =? tb + 1)%uint63 eqn:Ets; [discriminate|]. destruct (t' =? tb)%uint63 eqn:Etb; [discriminate|].
      destruct (Xdom t' rg' Ht') as [D0 | [D1 | [D2 | [D3 | [Db | [Dbs | Df]]]]]];
        [left; exact D0 | right; left; exact D1 | do 2 right; left; exact D2 | do 3 right; left; exact D3 | | | do 6 right; exact Df].
      + do 4 right. left. apply in_map_iff in Db as (g & <- & Hg). apply in_map_iff. exists g. split; [reflexivity|]. apply In_gremove. split; [exact Hg|].
        intros E. rewrite E, Uint63.eqb_refl in Etb. discriminate.
      + do 5 right. left. apply in_map_iff in Dbs as (g & <- & Hg). apply in_map_iff. exists g. split; [reflexivity|]. apply In_gremove. split; [exact Hg|].
        intros E. rewrite E, Uint63.eqb_refl in Ets. discriminate.
    - (* [comment removed for export] *) destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0).
      assert (Erg0 : rg0 = rg0_) by (fold F in Hrg0_; congruence). subst rg0_.
      exists (err_region K (t + 15) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len rg_dflt rg_pages]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0|].
      intros pn p' Hp'. rewrite iget_iset in Hp'. destruct (pn =? c_errcell K >> 12)%uint63 eqn:Epn.
      + apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_kind]. exact (Hpg0 _ _ Hpe).
      + exact (Hpg0 _ _ Hp').
    - (* [comment removed for export] *) destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
      exists (drop_below off rg1). rewrite !iget_iset. change ((1 =? 0)%uint63) with false. change ((1 =? 1)%uint63) with true. cbv iota.
      split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite !iget_iset, !iget_iremove. change ((2 =? 0)%uint63) with false. change ((2 =? 1)%uint63) with false.
      destruct (2 =? tb + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); pose proof (i63_range tb); rewrite to_Z_add_small in * by (change (to_Z 1%uint63) with 1; slia); change (to_Z 2%uint63) with 2 in *; change (to_Z 1%uint63) with 1 in *; slia|].
      destruct (2 =? tb)%uint63 eqn:Etb; [apply Uint63.eqb_spec in Etb; exfalso; pose proof (f_equal to_Z Etb); change (to_Z 2%uint63) with 2 in *; slia|].
      exact Xreg2.
    - (* [comment removed for export] *) rewrite !iget_iset, !iget_iremove. change ((3 =? 0)%uint63) with false. change ((3 =? 1)%uint63) with false.
      destruct (3 =? tb + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); pose proof (i63_range tb); rewrite to_Z_add_small in * by (change (to_Z 1%uint63) with 1; slia); change (to_Z 3%uint63) with 3 in *; change (to_Z 1%uint63) with 1 in *; slia|].
      destruct (3 =? tb)%uint63 eqn:Etb; [apply Uint63.eqb_spec in Etb; exfalso; pose proof (f_equal to_Z Etb); change (to_Z 3%uint63) with 3 in *; slia|].
      exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc).
      assert (rg0_ = rg0) by (fold F in Hrg0_; congruence). subst rg0_.
      exists (err_region K (t + 15) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len]. exact Hroc.
    - (* [comment removed for export] *) intros t' rg' pn p' ci c Ht' Hp' Hc. rewrite !iget_iset, !iget_iremove in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0.
      + injection Ht' as <-. unfold err_region in Hp' |- *. cbn [rg_pages rg_len] in Hp' |- *.
        rewrite iget_iset in Hp'. destruct (pn =? c_errcell K >> 12)%uint63 eqn:Epn.
        * apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_cells] in Hc. rewrite iget_iset in Hc.
          destruct (ci =? (c_errcell K land 4095) >> 3)%uint63 eqn:Eci.
          -- apply Uint63.eqb_spec in Eci. subst ci. rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095.
             destruct (err_page_ok_inv _ _ Hep) as (rg0b & pb & Hrg0b & Hir & _). fold F in Hrg0b. rewrite Hrg0M in Hrg0b. injection Hrg0b as <-.
             unfold in_region in Hir. rewrite !andb_true_iff in Hir. destruct Hir as [[[Hob _] _] Hir]. apply Uint63.leb_spec in Hir.
             apply Uint63.ltb_spec in Hob. change (to_Z off_bound) with (2 ^ 62) in Hob.
             rewrite Uint63.add_spec in Hir. change (to_Z 8%uint63) with 8 in Hir. change wB with (2 ^ 63) in Hir.
             pose proof (i63_range (c_errcell K)). pose proof (i63_range (rg_len rg0)).
             rewrite Z.mod_small in Hir by slia.
             split; [Z.div_mod_to_equations; nia | split; [Z.div_mod_to_equations; nia | intros v Ev; injection Hc as Ec; rewrite Ev in Ec; unfold err_cell in Ec; discriminate Ec]].
          -- exact (Xinb 0%uint63 rg0 _ pe ci c Hrg0M Hpe Hc).
        * exact (Xinb 0%uint63 rg0 pn p' ci c Hrg0M Hp' Hc).
      + destruct (t' =? 1)%uint63 eqn:E1.
        * injection Ht' as <-. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
          unfold drop_below. cbn [rg_len].
          unfold drop_page in Hc. cbn [fst snd] in Hc.
          destruct (pn =? off >> 12)%uint63.
          -- cbn [pg_cells] in Hc. destruct (keep_cells_ge_inv _ _ _ _ Hc) as [_ Hc']. fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc').
          -- fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc).
        * destruct (t' =? tb + 1)%uint63; [discriminate|]. destruct (t' =? tb)%uint63; [discriminate|].
          exact (Xinb t' rg' pn p' ci c Ht' Hp' Hc).
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0. rewrite !iget_iset, !iget_iremove in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|].
      destruct (t' =? 1)%uint63 eqn:E1.
      + injection Ht' as <-. apply Uint63.eqb_spec in E1. subst t'. fold F in Hrg1. destruct (Xkinds 1%uint63 rg1 Hrg1 Ht'0) as [Hdu1 Hku1].
        unfold drop_below. cbn [rg_dflt rg_pages]. split; [exact Hdu1|].
        intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
        unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hku1 _ _ Hp0).
      + destruct (t' =? tb + 1)%uint63; [discriminate|]. destruct (t' =? tb)%uint63; [discriminate|].
        exact (Xkinds t' rg' Ht' Ht'0).
    - (* [comment removed for export] *) rewrite Lby, Ecost'. slia.
    - (* [comment removed for export] *) rewrite Llen, Ecnt'. slia.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q)); [exact Hstk' | | rewrite Espu; slia].
      apply (stk_pres asegs (ms_mem ms)); [exact Hstk_hi|]. intros a Ha. apply Hpres; [|left; slia].
      destruct Hstk_hi as (_ & Hhi64 & _). rewrite Espu in Ha. slia.
    - repeat split; assumption.
    - exact Haux'.
    - exact Hinv'.
    - rewrite EerrA in Herr'. pose proof (stk_of_rw_cells asegs m' (errA A) [C4 errv] Herr') as Hs. cbn [cells_size csize] in Hs.
      replace (errA A + Z.of_nat 4) with (errA A + 4) in Hs by slia. exact Hs.
    - exact (HSH0 _ Hac' Hinv').
    - intros b Hb Hni. apply Lin; [exact (XLB0 b Hb Hni) | exact (Hgbid b Hb Hni)].
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - (* [comment removed for export] *) intros b Hb. destruct (XLBsub b (Lin' b Hb)) as [Hb0 | (g & Hg & ->)]; [left; exact Hb0 | right].
      exists g. split; [|reflexivity]. apply In_gremove. split; [exact Hg|]. intros E.
      apply Lnotp. replace (g_id gb) with (blk_id (g_id g, g_addr g, to_Z (g_size g))); [apply in_map; exact Hb|].
      cbn [blk_id fst]. rewrite <- Hgbt in E. f_equal.
      clear - XGtnd Hg Hgb E. induction G as [|x G' IH]; [destruct Hg|]. cbn [map] in XGtnd. pose proof (proj1 (NoDup_cons_iff _ _) XGtnd) as [Hn Hnd2].
      destruct Hg as [<-|Hg]; destruct Hgb as [<-|Hgb]; [reflexivity | | | exact (IH Hnd2 Hgb Hg)].
      + exfalso. apply Hn. rewrite E. apply in_map. exact Hgb.
      + exfalso. apply Hn. rewrite <- E. apply in_map. exact Hg.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      apply Hpres; [exact Ha | exact (Hclient_addr a Ha Hcl Hna)].
    - (* [comment removed for export] *) apply Forall_forall. intros f__ Hf__. pose proof (proj1 (Forall_forall _ _) XFFstk f__ Hf__) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf__) as [(KF1 & KF2 & KF3 & KF4 & KF5) (FB1 & FB2 & FB3 & FB4)].
      apply (stk_pres asegs (ms_mem ms)); [exact HsF|]. intros a__ Ha__.
      apply Hpres; [clear - Ha__ KF2 KF3 FB1 FB2; acb; unfold AFS_HDR, AIMG_TOP in *; slia| unfold aclient_addr; do 4 right; left; clear - Ha__ KF2 KF3; unfold AFS_HDR in *; slia].
  Qed.

  Theorem anode_free_null_sound : forall Q st st' rho msF mo,
    anode_free_null A st = Some st' ->
    to_Z (f_pc (a_F st)) = AFREE_STUB ->
    cells0_in A (f_mem (a_F st)) ->
    I2RA H IMX A Q st rho msF mo ->
    as_SR H (fun c' => exists rho', I2RA H IMX A Q st' rho' (cfg_ms c') (cfg_model c')) (mkCfg msF mo).
  Proof.
    intros Q st st' rho msF mo Hnode Hpc Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_free_null in Hnode.
    destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) 10)) as [z|] eqn:Ha0; [|discriminate].
    destruct (pop_cost 1 0 0 (a_cs st)) as [cs|] eqn:Hpop; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hguard; [|discriminate] end.
    cbv zeta in Hnode.
    destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
    destruct (set_errno K (a_n st + 15)%uint63 M1) as [M2|] eqn:HM2; [|discriminate].
    injection Hnode as <-.
    destruct (call_okn_inv _ _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv _ _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv. pose proof (conc63_inv _ _ Ha0) as Ea0.
    pose proof (pop_cost_inv _ _ _ _ _ Hpop) as Ecs.
    rewrite !andb_true_iff in Hguard. destruct Hguard as [[Hz0 Hchain] Hrook]. apply Uint63.eqb_spec in Hz0. subst z.
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    destruct (set_errno_inv _ _ _ _ HM2) as (rg0 & pe & Hrg0' & Hpe & Hpew & ->).
    rewrite !iget_iset in Hrg0'. change ((0 =? 1)%uint63) with false in Hrg0'. cbv iota in Hrg0'.
    rename Hrg0' into Hrg0M.
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (t := a_n st) in *.
    assert (Hag : agree t rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR.
    pose proof (canonR_R asegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    replace (f_pc F) with (f_pc (a_F st)) in Ems by reflexivity. rewrite Hpc in Ems.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 ATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    pose proof Hn59 as Hn59'. change (to_Z two59) with (2 ^ 59) in Hn59'.
    assert (Ea0v : rv rho F 10 = Z_to_bv 64 0).
    { rewrite Erv. change (of_Z 10) with 10%uint63. fold F in Ea0. rewrite Ea0. rewrite (dv_conc63 rho _ Xr0). reflexivity. }
    (* [comment removed for export] *)
    destruct (rw_c4_of_stk asegs _ _ Xerr) as [errv Herrv].
    assert (EerrA : bv_unsigned (rv rho F 4) + -164 = errA A).
    { rewrite Etpv. unfold errA. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      unfold ATP. rewrite Z.mod_small by slia. unfold AERRNO, ATP in Eerr. slia. }
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q) Xstk ltac:(rewrite Espu; slia)) as [Hstk_lo Hstk_hi].
    (* [comment removed for export] *)
    pose proof (i63_range (a_cost st)). pose proof (i63_range (c_cost K)).
    pose proof (i63_range (a_cnt st)). pose proof (i63_range (c_cnt K)). destruct (HK_caps A HK) as (Hcap1 & Hcap2 & Hcap3).
    (* [comment removed for export] *)
    destruct XAL as (done & Ecsq & HAL).
    assert (HCf : as_Cf H 0 <= as_AL H s /\ as_AL H s - as_Cf H 0 >= q_AL0 Q - csum H (done ++ [(1%uint63, 0%uint63, 0%uint63)])).
    { rewrite Ecs in Ecsq. pose proof XAL0 as B0. rewrite Ecsq, csum_app in B0. cbn [csum fold_right] in B0. fold (csum H cs) in B0.
      unfold cost1 in B0. change ((1 =? 0)%uint63) with false in B0. change ((1 =? 1)%uint63) with true in B0. cbv iota in B0. change (to_Z 0%uint63) with 0 in B0.
      pose proof (csum_nonneg H HHx cs). rewrite csum_app. cbn [csum fold_right]. unfold cost1. change ((1 =? 0)%uint63) with false. change ((1 =? 1)%uint63) with true. cbv iota.
      change (to_Z 0%uint63) with 0. slia. }
    destruct HCf as [HCf HAL'].
    (* [comment removed for export] *)
    destruct (chain_anyb_chain H IMX A HK HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hchain) as (CH & Hch).
    assert (Hch8 : as_chain H (ms_mem ms) (bv_unsigned (rv rho F 8)) CH) by exact Hch.
    (* [comment removed for export] *)
    eapply (ah_mono H HH).
    { eapply ((ah_free_null H HH) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q_F Q) (q_fc Q) msF (ms_mem ms) s LB (q_lo Q) (q_B Q) errv mo CH).
      - rewrite <- Ea0v. pose proof Xvis as XV. rewrite Ems in XV. exact XV.
      - exact Xheap.
      - exact Xak.
      - exact HCf.
      - exact Xaux.
      - rewrite Espu. slia.
      - exact Hstk_lo.
      - slia.
      - rewrite Espu. unfold AFREE_STACK in *. slia.
      - rewrite EerrA. exact Herrv.
      - exact Xinv.
      - exact Etpv.
      - rewrite Espu. clear - Hoff16 Hsp32 Hsp16 Hcs Hoff Est16. Z.div_mod_to_equations. slia.
      - exact Xac.
      - exact Hch8. }
    (* [comment removed for export] *)
    intros [msF' mo'] Hpost. unfold free_null_post in Hpost. cbn [cfg_ms cfg_model] in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & s'
                       & Evis' & Hak' & Hmpres' & Hinv' & Hstk' & Herr' & Haux' & Hpres & Hheap' & Hac' & HALs').
    cbn [cfg_ms cfg_model].
    set (L16 := [t0'; t1'; t2'; a0'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6'; errv]).
    set (rho' := rho_ext rho t L16).
    exists rho'.
    pose proof (i63_range t) as Ht.
    change (to_Z two59) with (2 ^ 59) in Hn59.
    assert (Hag' : agree t rho rho') by (apply agree_ext; [slia | slia | exact Xr0]).
    assert (Et16 : to_Z (t + 16)%uint63 = to_Z t + 16) by (rewrite to_Z_add_small; change (to_Z 16%uint63) with 16; slia).
    assert (Et15 : to_Z (t + 15)%uint63 = to_Z t + 15) by (rewrite to_Z_add_small; change (to_Z 15%uint63) with 15; slia).
    assert (EL16 : forall x (k : nat), (k < 16)%nat -> to_Z x = to_Z t + Z.of_nat k -> rho' x = nth k L16 w0).
    { intros x k Hk Hx. subst rho'. apply (rho_ext_at rho t L16 x k); [subst L16; cbn; slia | exact Hx]. }
    assert (Erho'e : rho' (t + 15)%uint63 = errv) by (rewrite (EL16 _ 15%nat); [reflexivity | slia | rewrite Et15; slia]).
    destruct Xnamed as [XG0in XLB0nd].
    assert (Hclient : forall a, 0 <= a < 2 ^ 64 -> client0 H Q a -> ~ named_addr Q a -> aclient_range H LB (bv_unsigned (rv rho F 2)) a 1).
    { intros a Ha Hcl Hna. rewrite Espu.
      unfold client0, aclient_addr in Hcl. destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
      - left. slia.
      - right. left. intros a' Ha'. replace a' with a by slia. exact Hst.
      - destruct (in_dec bptr_eq_dec (blk_id b) (map g_id (q_G0 Q))) as [Hi|Hni].
        + exfalso. apply Hna. apply in_map_iff in Hi as (g0 & Eg & Hg0).
          pose proof (proj1 (Forall_forall _ _) XG0in g0 Hg0) as Hg0in.
          pose proof (nodup_ids_eq _ b _ XLB0nd Hb Hg0in ltac:(rewrite <- Eg; reflexivity)) as ->.
          exists g0. split; [exact Hg0|]. left. cbn [blk_addr blk_size fst snd] in Hr. exact Hr.
        + right. right. left. exists b. split; [exact (XLB0 b Hb Hni)|]. slia.
      - destruct (in_dec bptr_eq_dec (blk_id b) (map g_id (q_G0 Q))) as [Hi|Hni].
        + exfalso. apply Hna. apply in_map_iff in Hi as (g0 & Eg & Hg0).
          pose proof (proj1 (Forall_forall _ _) XG0in g0 Hg0) as Hg0in.
          pose proof (nodup_ids_eq _ b _ XLB0nd Hb Hg0in ltac:(rewrite <- Eg; reflexivity)) as ->.
          exists g0. split; [exact Hg0|]. right. cbn [blk_addr blk_size fst snd] in Hr. exact Hr.
        + right. right. right. left. exists b. split; [exact (XLB0 b Hb Hni)|]. slia.
      - do 4 right. left. slia.
      - do 5 right. left. slia.
      - do 6 right. slia. }
    assert (Hclient_addr : forall a, 0 <= a < 2 ^ 64 -> client0 H Q a -> ~ named_addr Q a -> aclient_addr H LB (bv_unsigned (rv rho F 2)) a).
    { intros a Ha Hcl Hna. eapply aclient_range_addr; [exact (Hclient a Ha Hcl Hna) | slia]. }
    (* [comment removed for export] *)
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> aclient_addr H LB (bv_unsigned (rv rho F 2)) a ->
                     rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a)
                     /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hc. destruct (Hpres a Ha Hc) as [E W]. split; [apply rview_eq_of_mem; exact E | exact W]. }
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) a0'
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    exists s', LB, G, FF, XS, ms1.
    assert (HRn' : Rn asegs IM (t + 16)%uint63 rho'
              (FS (ret_of l) (clobber clob15 t (f_regs F))
                  (iset 0 (err_region K (t + 15) rg0 pe) (iset 1 (drop_below off rg1) (f_mem F))) None)
              ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree t rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Et16; slia]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z t + 16 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Et16; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''old : forall x, to_Z x < to_Z t -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by slia. subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; slia); exact Xr1).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) a0'
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; a0';
                      a1'; a2'; a3'; a4'; a5'; a6'; a7'; rv rho F 18; rv rho F 19; rv rho F 20; rv rho F 21; rv rho F 22; rv rho F 23;
                      rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; t3'; t4'; t5'; t6']).
        apply R_regs_of_match; [exact Hrho''0 | reflexivity |].
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) (rv rho F 5) (rv rho F 6) (rv rho F 7) (rv rho F 8) (rv rho F 9) (rv rho F 10)
                     (rv rho F 11) (rv rho F 12) (rv rho F 13) (rv rho F 14) (rv rho F 15) (rv rho F 16) (rv rho F 17) (rv rho F 18) (rv rho F 19) (rv rho F 20)
                     (rv rho F 21) (rv rho F 22) (rv rho F 23) (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) (rv rho F 28) (rv rho F 29) (rv rho F 30) (rv rho F 31))
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; rv rho F 5; rv rho F 6; rv rho F 7; rv rho F 8; rv rho F 9; rv rho F 10;
                      rv rho F 11; rv rho F 12; rv rho F 13; rv rho F 14; rv rho F 15; rv rho F 16; rv rho F 17; rv rho F 18; rv rho F 19; rv rho F 20;
                      rv rho F 21; rv rho F 22; rv rho F 23; rv rho F 24; rv rho F 25; rv rho F 26; rv rho F 27; rv rho F 28; rv rho F 29; rv rho F 30; rv rho F 31]) in HR''.
        pose proof (regs_match_of_R _ _ _ _ _ _ _ _ _ _ _ HR'') as Hpre.
        assert (Hnd15 : List.NoDup clob15) by (apply nodupb_spec; reflexivity).
        assert (Hcl : forall k : int, iget k (clobber clob15 t (f_regs F)) =
                      match index_of k clob15 with
                      | Some i => Some (FV (of_Z (to_Z t + Z.of_nat i)) w_zero)
                      | None => iget k (f_regs F) end).
        { intros k. apply iget_clobber; [exact Hnd15 | cbn [length clob15]; slia]. }
        apply regs_match_intro. cbn [seq].
        repeat (apply Forall_cons || apply Forall_nil);
          cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ];
          match goal with |- _ = dv _ (FxState.rget ?FF ?k) =>
            let kk := eval vm_compute in k in change k with kk; rewrite (rget_regs' FF kk eq_refl) end;
          cbn [f_regs].
        all: try (rewrite Hcl;
                  match goal with |- _ = dv _ match match ?ix with _ => _ end with _ => _ end =>
                    let ii := eval vm_compute in ix in change ix with ii end; cbv iota).
        all: first
          [ (* [comment removed for export] *)
            match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); slia);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia);
              rewrite (EL16 (of_Z (to_Z t1 + Z.of_nat i)) i); [reflexivity | slia | rewrite Etag; slia]
            end
          | (* [comment removed for export] *)
            match goal with |- rv _ _ ?kz = dv _ match iget ?ki (f_regs ?FF) with _ => _ end =>
              rewrite <- (rget_regs' FF ki eq_refl);
              let kn := eval vm_compute in (Z.to_nat kz) in
              let HP := fresh "HP" in
              pose proof (Hpre kn ltac:(slia)) as HP; cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in HP; exact HP
            end
          ].
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        cbn [f_mem ms_mem].
        destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0_. rewrite Hrg0M in Hrg0_. injection Hrg0_ as <-.
        destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
        apply mem_ok_parts.
        + intros t' rg' Ht'. rewrite !iget_iset in Ht'.
          destruct (t' =? 0)%uint63 eqn:E0.
          * (* [comment removed for export] *) apply Uint63.eqb_spec in E0. subst t'. injection Ht' as <-.
            eapply (region0_part asegs IM rho'' Hrho''0 IMX eq_refl HIMX HWRX K (ms_mem ms) m' rg0 pe (t + 15)%uint63 errv
                      (fun c => 0 <= c /\ c + 8 <= AIMG_TOP /\ ((exists x, In x (c_xw K) /\ to_Z x = c)
                                                           \/ (exists cc, In (of_Z c, cc) (c_ro K) /\ aconst_pin_b (of_Z c) cc = false)))).
            -- exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0M).
            -- exact Hd0.
            -- exact Hpg0.
            -- intros pn p0 ci c Hp0 Hc. pose proof (i63_range pn) as Rpn. pose proof (i63_range ci) as Rci.
               destruct (Xinb 0%uint63 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hcb [Hci512 _]]. rewrite Hlen0 in Hcb.
               destruct (Hc0 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hx | [He | (cc & Hcc)]].
               ** left. split; [slia|]. split; [clear -Hcb; unfold AIMG_TOP in *; slia|]. left; exact Hx.
               ** right; left; exact He.
               ** destruct (aconst_pin_b (of_Z (to_Z pn * 4096 + to_Z ci * 8)) cc) eqn:Epin.
                  --- (* [comment removed for export] *)
                      right; right. destruct (aconst_pin_sound m' _ cc Hac' Epin) as (sl & -> & Hsl).
                      assert (Ea : to_Z (of_Z (to_Z pn * 4096 + to_Z ci * 8)) = to_Z pn * 4096 + to_Z ci * 8)
                        by (apply toZ_of_Z_small; clear -Hcb Rpn Rci; unfold AIMG_TOP in *; slia).
                      pose proof (ro_okb_sound K (f_mem F) rg0 _ (CB sl) pn p0 ci c Hrook Hrg0M Hcc Hp0 Hc (eq_sym Ea) ltac:(clear -Hci512 Rci; slia)) as ->.
                      exists sl. split; [reflexivity|]. intros j Hj. pose proof (Hsl rho'' j Hj) as T. rewrite Ea in T. exact T.
                  --- left. split; [slia|]. split; [clear -Hcb; unfold AIMG_TOP in *; slia|]. right. exists cc. split; [exact Hcc | exact Epin].
            -- intros c a (Hc0' & Hc8 & [(x & Hx & <-) | (cc & Hcc & Hnp)]) Ha.
               ++ clear - Hkeep Hx Ha Hc0' Hc8 HK Espu Hoff Hcs Hlsp Hhl ACEILB. hk_xw x Hx.
                  apply (proj1 (Hkeep a ltac:(unfold AIMG_TOP in *; slia) ltac:(right; left; eapply aimg8_b_spec; [|exact Ha]; unfold aimg8_b; unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in *;
                           rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le; slia))).
               ++ destruct (aimg8_b c) eqn:E8.
                  ** apply (proj1 (Hkeep a ltac:(unfold AIMG_TOP in *; slia) ltac:(right; left; exact (aimg8_b_spec _ _ E8 Ha)))).
                  ** pose proof (HROC _ _ Xac Hac' Xinv Hinv' (of_Z c) cc Hcc) as E. rewrite toZ_of_Z_small in E by (unfold AIMG_TOP in *; slia).
                     specialize (E E8 Hnp (a - c) ltac:(slia)). replace (c + (a - c)) with a in E by slia. exact E.
            -- exact Hpe.
            -- exact Hinv'.
            -- rewrite EerrA in Herr'. exact Herr'.
            -- rewrite dv_tag_zero by (rewrite Et15; slia). rewrite Erho'' by (rewrite Et15; slia). exact Erho'e.
            -- exact Eerr8.
            -- exact Ebi.
            -- destruct (err_page_ok_inv _ _ Hep) as (rg0b & pb & Hrg0b & Hir & _). fold F in Hrg0b. rewrite Hrg0M in Hrg0b. injection Hrg0b as <-.
               unfold in_region in Hir. rewrite !andb_true_iff in Hir. destruct Hir as [[[Hob _] _] Hir]. apply Uint63.leb_spec in Hir.
               apply Uint63.ltb_spec in Hob. change (to_Z off_bound) with (2 ^ 62) in Hob.
               rewrite Uint63.add_spec in Hir. change (to_Z 8%uint63) with 8 in Hir. change wB with (2 ^ 63) in Hir.
               pose proof (i63_range (c_errcell K)). pose proof (i63_range (rg_len rg0)). rewrite Z.mod_small in Hir by slia. exact Hir.
            -- rewrite Hlen0. reflexivity.
          * destruct (t' =? 1)%uint63 eqn:E1.
            -- (* [comment removed for export] *) apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
               destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
               apply (stack_part asegs IM rho'' (ms_mem ms) m' rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q)).
               ++ exact Erho''1.
               ++ exact Hlo1.
               ++ exact Hd1.
               ++ exact Hkd1.
               ++ rewrite Hlen1. reflexivity.
               ++ rewrite Hlen1. slia.
               ++ clear - Hoff16 Hoff. Z.div_mod_to_equations. slia.
               ++ exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1).
               ++ exact Xstk.
               ++ slia.
               ++ rewrite <- Espu. exact Hstk'.
               ++ intros a Ha. destruct Xstk as (_ & H64 & _). apply Hkeep; [slia | left; rewrite Espu; slia].
            -- (* [comment removed for export] *)
               assert (Hne0 : t' <> 0%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E0; discriminate).
               assert (Hne1 : t' <> 1%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E1; discriminate).
               apply (old_parts H IMX A HK HHx HSH0 _ _ _ _ _ _ _ _ _ _ _ rho'' m' LB (bv_unsigned (rv rho F 2)) [] t' rg' X).
               ++ intros x Hx. apply Erho''old. exact Hx.
               ++ exact Hkeep.
               ++ rewrite Espu. slia.
               ++ intros g Hg _. exact (proj1 (proj1 (Forall_forall _ _) XGin g Hg)).
               ++ intros b Hb. exact Hb.
               ++ exact Hac'.
               ++ exact Hinv'.
               ++ exact Ht'.
               ++ exact Hne0.
               ++ exact Hne1.
               ++ intros g _ [].
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2. rewrite !iget_iset in Hi1, Hi2.
          assert (Hold : forall t' rg',
                    (if (t' =? 0)%uint63 then Some (err_region K (t + 15) rg0 pe)
                     else if (t' =? 1)%uint63 then Some (drop_below off rg1) else iget t' (f_mem F)) = Some rg' ->
                    exists rg, iget t' (f_mem F) = Some rg /\ rg_lo rg = rg_lo rg' /\ rg_len rg = rg_len rg').
          { intros t' rg' Ht'.
            destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; subst t'; injection Ht' as <-; exists rg0; split; [exact Hrg0M | split; reflexivity]|].
            destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; subst t'; injection Ht' as <-; exists rg1; split; [exact Hrg1 | split; reflexivity]|].
            exists rg'. split; [exact Ht' | split; reflexivity]. }
          destruct (Hold t1 r1 Hi1) as (q1 & Hq1 & El1 & En1). destruct (Hold t2 r2 Hi2) as (q2 & Hq2 & El2 & En2).
          rewrite <- El1, <- En1, <- El2, <- En2. exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
    (* [comment removed for export] *)
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mkc f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS ms1].
    - exact Evis'.
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr2 | change (to_Z 2%uint63) with 2; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr3 | change (to_Z 3%uint63) with 3; slia].
    - eapply agree_trans; [exact Xag | exact Hag' | slia].
    - rewrite Et16. slia.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmpres').
    - exact Hheap'.
    - eapply (RFS_via_apres H HH); [exact Xrfs | exact Hpres].
    - exact Hac'.
    - (* [comment removed for export] *) destruct Xst0 as (g & G1' & G2' & G3' & AD). exists g. split; [exact G1'|]. split; [exact G2'|]. split; [exact G3'|].
      destruct AD as [ADn SH]. split; [exact ADn|]. eapply (apres_SHAD H); [exact Hpres | exact SH |].
      do 6 right. rewrite shadow_of_length by slia. pose proof (SHAD_aligned _ _ _ SH) as [_ G8].
      assert (M1 : sh aceil <= sh g) by (apply sh_mono; slia).
      assert (M2 : sh g + nsh (q_shi Q - g) <= AHI_LO).
      { clear - G1' G2' G8. unfold nsh, sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia. }
      slia.
    - eapply (chain_via_apres H HH); [exact Xch | exact Hpres |]. intros fp ra Hin. rewrite Espu. specialize (XCH0 fp ra Hin). slia.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - (* [comment removed for export] *) exists (done ++ [(1%uint63, 0%uint63, 0%uint63)]). split; [rewrite Ecsq, Ecs, <- app_assoc; reflexivity | slia].
    - exact XAL0.
    - (* [comment removed for export] *) exact XG.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hsh).
      pose proof (i63_range (g_tag g)). destruct Xn0 as [Hn4 Hn60].
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      split; [exact Hin|]. split; [subst rho'; rewrite rho_ext_old by slia; exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
      split; [rewrite Et16; slia|]. split.
      + exists rgg. rewrite !iget_iset.
        destruct (g_tag g =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); change (to_Z 0%uint63) with 0 in *; slia|].
        destruct (g_tag g =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); change (to_Z 1%uint63) with 1 in *; slia|].
        split; [exact Hgg|]. repeat split; assumption.
      + intros rg' Hrg'. rewrite !iget_iset in Hrg'.
        destruct (g_tag g + 1 =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); rewrite Etg1 in *; change (to_Z 0%uint63) with 0 in *; slia|].
        destruct (g_tag g + 1 =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); rewrite Etg1 in *; change (to_Z 1%uint63) with 1 in *; slia|].
        destruct (Hsh rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia); exact Hrs|].
        eapply (apres_addressable H); [exact Hpres | exact Had' | exact Hin].
    - exact XGnd.
    - exact XGtnd.
    - exact XGnew.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
      pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _ & Hsz & _).
      pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
      apply (stk_pres asegs (ms_mem ms)); [exact Hs|]. intros a Ha. apply Hpres; [slia|].
      unfold aclient_addr. do 2 right. left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr blk_size fst snd]; slia].
    - exact XFF.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkf & Half & Hdff) & (rgs' & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)).
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
      split; [subst rho'; rewrite rho_ext_old by slia; exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia); exact Hf1|].
      split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; slia); exact Hf2|]. split; [exact Hk|]. split; [exact Htg1|]. split; [rewrite Et16; slia|].
      assert (NT : forall x, (to_Z x = to_Z (f_tag f) \/ to_Z x = to_Z (f_tag f) + 1 \/ to_Z x = to_Z (f_tag f) + 2) ->
                   (x =? 0)%uint63 = false /\ (x =? 1)%uint63 = false).
      { intros x Hx. repeat split;
          (destruct (Uint63.eqb x _) eqn:E; [|reflexivity]; apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E;
           change (to_Z 0%uint63) with 0 in E; change (to_Z 1%uint63) with 1 in E; exfalso; clear - Hx E Htg1; slia). }
      destruct (NT (f_tag f) ltac:(left; reflexivity)) as (N0 & N1).
      destruct (NT (f_tag f + 1)%uint63 ltac:(right; left; exact Etg1)) as (M0 & M1').
      destruct (NT (f_tag f + 2)%uint63 ltac:(right; right; exact Etg2)) as (P0 & P1).
      split; [exists rgf; rewrite !iget_iset, N0, N1; split; [exact Hgf|]; repeat split; assumption|].
      split; [exists rgs'; rewrite !iget_iset, M0, M1'; split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite !iget_iset, P0, P1; exact Hflg|].
      repeat split; assumption.
    - exact XFFnd.
    - exact XFFtnd.
    - exact XTsep.
    - exact XFFlen.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; left; exact E0|].
      destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; right; left; exact E1|].
      exact (Xdom t' rg' Ht').
    - (* [comment removed for export] *) destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0).
      assert (Erg0 : rg0 = rg0_) by (fold F in Hrg0_; congruence). subst rg0_.
      exists (err_region K (t + 15) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len rg_dflt rg_pages]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0|].
      intros pn p' Hp'. rewrite iget_iset in Hp'. destruct (pn =? c_errcell K >> 12)%uint63 eqn:Epn.
      + apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_kind]. exact (Hpg0 _ _ Hpe).
      + exact (Hpg0 _ _ Hp').
    - (* [comment removed for export] *) destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
      exists (drop_below off rg1). rewrite !iget_iset. change ((1 =? 0)%uint63) with false. change ((1 =? 1)%uint63) with true. cbv iota.
      split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((2 =? 0)%uint63) with false. change ((2 =? 1)%uint63) with false. exact Xreg2.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((3 =? 0)%uint63) with false. change ((3 =? 1)%uint63) with false. exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc).
      assert (rg0_ = rg0) by (fold F in Hrg0_; congruence). subst rg0_.
      exists (err_region K (t + 15) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len]. exact Hroc.
    - (* [comment removed for export] *) intros t' rg' pn p' ci c Ht' Hp' Hc. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0.
      + injection Ht' as <-. unfold err_region in Hp' |- *. cbn [rg_pages rg_len] in Hp' |- *.
        rewrite iget_iset in Hp'. destruct (pn =? c_errcell K >> 12)%uint63 eqn:Epn.
        * apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_cells] in Hc. rewrite iget_iset in Hc.
          destruct (ci =? (c_errcell K land 4095) >> 3)%uint63 eqn:Eci.
          -- apply Uint63.eqb_spec in Eci. subst ci. rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095.
             destruct (err_page_ok_inv _ _ Hep) as (rg0b & pb & Hrg0b & Hir & _). fold F in Hrg0b. rewrite Hrg0M in Hrg0b. injection Hrg0b as <-.
             unfold in_region in Hir. rewrite !andb_true_iff in Hir. destruct Hir as [[[Hob _] _] Hir]. apply Uint63.leb_spec in Hir.
             apply Uint63.ltb_spec in Hob. change (to_Z off_bound) with (2 ^ 62) in Hob.
             rewrite Uint63.add_spec in Hir. change (to_Z 8%uint63) with 8 in Hir. change wB with (2 ^ 63) in Hir.
             pose proof (i63_range (c_errcell K)). pose proof (i63_range (rg_len rg0)).
             rewrite Z.mod_small in Hir by slia.
             split; [Z.div_mod_to_equations; nia | split; [Z.div_mod_to_equations; nia | intros v Ev; injection Hc as Ec; rewrite Ev in Ec; unfold err_cell in Ec; discriminate Ec]].
          -- exact (Xinb 0%uint63 rg0 _ pe ci c Hrg0M Hpe Hc).
        * exact (Xinb 0%uint63 rg0 pn p' ci c Hrg0M Hp' Hc).
      + destruct (t' =? 1)%uint63 eqn:E1.
        * injection Ht' as <-. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
          unfold drop_below. cbn [rg_len].
          unfold drop_page in Hc. cbn [fst snd] in Hc.
          destruct (pn =? off >> 12)%uint63.
          -- cbn [pg_cells] in Hc. destruct (keep_cells_ge_inv _ _ _ _ Hc) as [_ Hc']. fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc').
          -- fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc).
        * exact (Xinb t' rg' pn p' ci c Ht' Hp' Hc).
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|].
      destruct (t' =? 1)%uint63 eqn:E1.
      + injection Ht' as <-. apply Uint63.eqb_spec in E1. subst t'. fold F in Hrg1. destruct (Xkinds 1%uint63 rg1 Hrg1 Ht'0) as [Hdu1 Hku1].
        unfold drop_below. cbn [rg_dflt rg_pages]. split; [exact Hdu1|].
        intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
        unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hku1 _ _ Hp0).
      + exact (Xkinds t' rg' Ht' Ht'0).
    - exact Xcost.
    - exact Xcnt.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q)); [exact Hstk' | | rewrite Espu; slia].
      apply (stk_pres asegs (ms_mem ms)); [exact Hstk_hi|]. intros a Ha. apply Hpres; [|left; slia].
      destruct Hstk_hi as (_ & Hhi64 & _). rewrite Espu in Ha. slia.
    - repeat split; assumption.
    - exact Haux'.
    - exact Hinv'.
    - rewrite EerrA in Herr'. pose proof (stk_of_rw_cells asegs m' (errA A) [C4 errv] Herr') as Hs. cbn [cells_size csize] in Hs.
      replace (errA A + Z.of_nat 4) with (errA A + 4) in Hs by slia. exact Hs.
    - exact (HSH0 _ Hac' Hinv').
    - exact XLB0.
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - exact XLBsub.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      apply Hpres; [exact Ha | exact (Hclient_addr a Ha Hcl Hna)].
    - (* [comment removed for export] *) apply Forall_forall. intros f__ Hf__. pose proof (proj1 (Forall_forall _ _) XFFstk f__ Hf__) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf__) as [(KF1 & KF2 & KF3 & KF4 & KF5) (FB1 & FB2 & FB3 & FB4)].
      apply (stk_pres asegs (ms_mem ms)); [exact HsF|]. intros a__ Ha__.
      apply Hpres; [clear - Ha__ KF2 KF3 FB1 FB2; acb; unfold AFS_HDR, AIMG_TOP in *; slia| unfold aclient_addr; do 4 right; left; clear - Ha__ KF2 KF3; unfold AFS_HDR in *; slia].
  Qed.
End NodeF.
