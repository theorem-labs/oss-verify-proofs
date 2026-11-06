(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_SR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2U Require Import
  I2Inv I2NodeLib I2NodeMem I2NodeM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Section NodeA.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Variable IMX : fimage.
  Variable K : i2consts.
  Let IM := im_ro IMX.
  Let RO := ro_of K.
  Hypothesis HK : K_ok K = true.
  Hypothesis HHx : heap_sr_hyps_x H.
  Hypothesis HIMX : image_ok usegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.

  Let HH : heap_sr_hyps H := proj1 HHx.

  Ltac hk_err :=
    let E1 := fresh "Eerr" in let E2 := fresh "Eerr8" in let E3 := fresh "Ebi" in let E4 := fresh "Etp" in
    let E5 := fresh "Em1" in let E6 := fresh "Em2" in let E7 := fresh "Est16" in let E8 := fresh "Est40" in
    destruct (HK_err K HK) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8);
    pose proof (i63_range (c_errbi K)); pose proof (i63_range (c_errcell K)); pose proof (i63_range (c_stack K));
    pose proof (i63_range (c_mstack K)).
  Ltac hk_xw c Hc :=
    let X := fresh "Xw" in
    pose proof (xw_cell_ok_spec c (HK_xw K HK c Hc)) as X;
    unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in X;
    destruct X as (? & ? & ? & ? & ? & ? & ? & ?); pose proof (i63_range c).

  Hypothesis HROC : ro_const H K.

  Theorem node_aalloc_sound : forall Q st st' rho ms mo,
    node_aalloc K st = Some st' ->
    to_Z (f_pc (i_F st)) = RAALLOC_SYM ->
    cells0_in K (f_mem (i_F st)) ->
    I2R H IMX K Q st rho ms mo ->
    hs_SR H (fun c' => exists rho', I2R H IMX K Q st' rho' (cfg_ms c') (cfg_model c')) (mkCfg ms mo).
  Proof.
    intros Q st st' rho ms mo Hnode Hpc Hc0 (s & LB & G & X).
    (* [comment removed for export] *)
    unfold node_aalloc in Hnode.
    destruct (call_ok K st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (conc63 (FxState.rget (i_F st) 10)) as [al|] eqn:Haal; [|discriminate].
    destruct (conc63 (FxState.rget (i_F st) 11)) as [n|] eqn:Ha0; [|discriminate].
    destruct (log2_al al) as [lg|] eqn:Hlg; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hguard; [|discriminate] end.
    destruct (drop_stack off (f_mem (i_F st))) as [M1|] eqn:HM1; [|discriminate].
    destruct (set_errno K (i_n st + 15)%uint63 (iset (i_n st) (blk_region n lg iempty) M1)) as [M2|] eqn:HM2; [|discriminate].
    injection Hnode as <-.
    destruct (call_ok_inv _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_inv _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv. pose proof (conc63_inv _ _ Ha0) as Ea0. pose proof (conc63_inv _ _ Haal) as Eaal.
    rewrite !andb_true_iff in Hguard. destruct Hguard as [[[[[[[[Hn1 Hn32] Hc3] Hc1] Hc2] Hk1] Hk2] Hb1] Hb2].
    apply Uint63.leb_spec in Hn1. apply Uint63.ltb_spec in Hn32. change (to_Z 1%uint63) with 1 in Hn1. change (to_Z RMMAP_THRESHOLD) with 131052 in Hn32.
    apply Uint63.leb_spec in Hc1. apply Uint63.leb_spec in Hc2. apply Uint63.leb_spec in Hc3.
    apply Uint63.leb_spec in Hk1. apply Uint63.leb_spec in Hk2. apply Uint63.leb_spec in Hb1. apply Uint63.leb_spec in Hb2.
    (* [comment removed for export] *)
    assert (Hal : (al = 16%uint63 /\ lg = 4%uint63) \/ (al = 32%uint63 /\ lg = 5%uint63) \/ (al = 64%uint63 /\ lg = 6%uint63)).
    { unfold log2_al in Hlg. destruct (al =? 16)%uint63 eqn:E16; [apply Uint63.eqb_spec in E16; injection Hlg as <-; left; split; [exact E16 | reflexivity]|].
      destruct (al =? 32)%uint63 eqn:E32; [apply Uint63.eqb_spec in E32; injection Hlg as <-; right; left; split; [exact E32 | reflexivity]|].
      destruct (al =? 64)%uint63 eqn:E64; [apply Uint63.eqb_spec in E64; injection Hlg as <-; right; right; split; [exact E64 | reflexivity]|]. discriminate. }
    assert (Hal64 : 16 <= to_Z al <= 64 /\ 4 <= to_Z lg <= 6).
    { destruct Hal as [[-> ->] | [[-> ->] | [-> ->]]]; cbn; slia. }
    destruct Hal64 as (Halr & Hlgr).
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    destruct (set_errno_inv _ _ _ _ HM2) as (rg0 & pe & Hrg0' & Hpe & Hpew & ->).
    rewrite iget_iset in Hrg0'.
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xag Xn0 Xheap Xkrel Xmp XG XGin XGnd XGtnd XGnew XGstk Xdom Xreg0 Xreg1 Xro Xinb Xkinds
                    Xcost Xcnt Xbig Xstk Xlo Xaux Xinv Xerr XLB0 XLB0h Xnamed XLBsub Xframe].
    set (F := i_F st) in *. set (t := i_n st) in *.
    assert (Hag : agree t rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR.
    (* [comment removed for export] *)
    pose proof (canonR_R usegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    replace (f_pc F) with (f_pc (i_F st)) in Ems by reflexivity. rewrite Hpc in Ems.
    (* [comment removed for export] *)
    pose proof (R_regs _ _ _ _ _ HR) as Hregs.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. destruct Xlo as (Hh & Hl & HB & _ & HB64). pose proof hceil_pos.
      pose proof (i63_range off). rewrite (adr_wa rho 1%uint63 _ _ Xr1); slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 RATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Ea0v : rv rho F 11 = Z_to_bv 64 (to_Z n)).
    { rewrite Erv. change (of_Z 11) with 11%uint63. fold F in Ea0. rewrite Ea0. apply dv_conc63. exact Xr0. }
    assert (Eaalv : rv rho F 10 = Z_to_bv 64 (to_Z al)).
    { rewrite Erv. change (of_Z 10) with 10%uint63. fold F in Eaal. rewrite Eaal. apply dv_conc63. exact Xr0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    (* [comment removed for export] *)
    destruct (rw_c4_of_stk usegs _ _ Xerr) as [errv Herrv].
    assert (EerrA : bv_unsigned (rv rho F 4) + -164 = errA K).
    { rewrite Etpv. unfold errA. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      unfold RATP. rewrite Z.mod_small by slia. unfold RERRNO in Eerr. slia. }
    (* [comment removed for export] *)
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & HB64).
    destruct (stk_split usegs _ (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q) Xstk ltac:(rewrite Espu; pose proof (i63_range off); slia)) as [Hstk_lo Hstk_hi].
    (* [comment removed for export] *)
    assert (Hbig1 : HeapSR_iface.big1 (to_Z n) = to_Z (I2Run.big1 n)).
    { unfold HeapSR_iface.big1, I2Run.big1, HeapSR_iface.BIGB, I2Run.BIGB.
      destruct (2028 <? n)%uint63 eqn:E.
      - apply Uint63.ltb_spec in E. change (to_Z 2028%uint63) with 2028 in E. destruct (Z.ltb_spec 2028 (to_Z n)); [reflexivity | slia].
      - assert (Hnlt : ~ to_Z 2028%uint63 < to_Z n) by (intros Hlt; apply Uint63.ltb_spec in Hlt; congruence).
        change (to_Z 2028%uint63) with 2028 in Hnlt. destruct (Z.ltb_spec 2028 (to_Z n)); [slia | reflexivity]. }
    pose proof (i63_range (i_cost st)). pose proof (i63_range (c_cost K)). pose proof (i63_range n).
    pose proof (i63_range (i_cnt st)). pose proof (i63_range (c_cnt K)). pose proof (i63_range (i_big st)). pose proof (i63_range (c_big K)).
    pose proof (i63_range (I2Run.big1 n)). pose proof (i63_range al). destruct (HK_caps K HK) as (Hcap1 & Hcap2 & Hcap3).
    assert (Enal : to_Z (n + al)%uint63 = to_Z n + to_Z al).
    { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    rewrite Enal in Hn32.
    assert (Ecost : to_Z (i_cost st + n)%uint63 = to_Z (i_cost st) + to_Z n).
    { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    assert (Ecostal : to_Z (i_cost st + n + al)%uint63 = to_Z (i_cost st) + to_Z n + to_Z al).
    { rewrite Uint63.add_spec, Ecost. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    assert (Hbig1al : HeapSR_iface.big1 (to_Z n + to_Z al) = to_Z (I2Run.big1 (n + al)%uint63)).
    { unfold HeapSR_iface.big1, I2Run.big1, HeapSR_iface.BIGB, I2Run.BIGB.
      destruct (2028 <? n + al)%uint63 eqn:E.
      - apply Uint63.ltb_spec in E. rewrite Enal in E. change (to_Z 2028%uint63) with 2028 in E. destruct (Z.ltb_spec 2028 (to_Z n + to_Z al)); [reflexivity | slia].
      - assert (Hnlt : ~ to_Z 2028%uint63 < to_Z (n + al)%uint63) by (intros Hlt; apply Uint63.ltb_spec in Hlt; congruence).
        rewrite Enal in Hnlt. change (to_Z 2028%uint63) with 2028 in Hnlt. destruct (Z.ltb_spec 2028 (to_Z n + to_Z al)); [slia | reflexivity]. }
    assert (Hbigmono : to_Z (I2Run.big1 n) <= to_Z (I2Run.big1 (n + al)%uint63)).
    { unfold I2Run.big1, I2Run.BIGB. destruct (2028 <? n)%uint63 eqn:E1; destruct (2028 <? n + al)%uint63 eqn:E2; cbn; try slia.
      apply Uint63.ltb_spec in E1. assert (Hn2' : ~ to_Z 2028%uint63 < to_Z (n + al)%uint63) by (intros Hlt; apply Uint63.ltb_spec in Hlt; congruence).
      rewrite Enal in Hn2'. slia. }
    pose proof (i63_range (I2Run.big1 (n + al)%uint63)).
    assert (Ecnt : to_Z (i_cnt st + 1)%uint63 = to_Z (i_cnt st) + 1).
    { rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    assert (Hb1le : forall x, 0 <= to_Z (I2Run.big1 x) <= 1) by (intros x; unfold I2Run.big1; destruct (I2Run.BIGB <? x)%uint63; cbn; slia).
    pose proof (Hb1le n). pose proof (Hb1le (n + al)%uint63).
    assert (Ebig : to_Z (i_big st + I2Run.big1 n)%uint63 = to_Z (i_big st) + to_Z (I2Run.big1 n)).
    { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    assert (Ebigal : to_Z (i_big st + I2Run.big1 (n + al))%uint63 = to_Z (i_big st) + to_Z (I2Run.big1 (n + al)%uint63)).
    { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    rewrite Ecostal in Hc1. rewrite Ecnt in Hk1. rewrite Ebigal in Hb1.
    assert (Halloc : hs_alloc_ok H s LB (to_Z n + to_Z al)).
    { apply (HH_alloc_ok H HH s LB (ms_mem ms) (to_Z n + to_Z al) Xheap); [slia | slia | slia |]. rewrite Hbig1al. slia. }
    (* [comment removed for export] *)
    rewrite Ems.
    eapply (sr_mono H HH).
    { eapply (proj1 (proj2 (proj2 HHx))); try eassumption.
      - rewrite Espu. slia.
      - rewrite Espu. unfold RAALLOC_STACK, RMALLOC_STACK. unfold RREALLOC_STACK, RMALLOC_STACK in Em1. pose proof (i63_range off). slia.
      - rewrite EerrA. exact Herrv.
      - clear -Hal. destruct Hal as [[-> _] | [[-> _] | [-> _]]]; [exists 4 | exists 5 | exists 6]; (split; [slia | reflexivity]). }
    (* [comment removed for export] *)
    intros [ms' mo'] Hpost. unfold aalloc_sr_post in Hpost. cbn [cfg_ms cfg_model] in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & A & junk & p & s'
                       & Ems' & Hkrel' & Hmpres' & Hinv' & Hstk' & Herr' & Haux' & Hpres & Hrng & HAal & Hheap' & Hblk).
    cbn [cfg_ms cfg_model]. subst ms'.
    set (L16 := [wa A; t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6'; errv']).
    set (rho' := rho_ext rho t L16).
    exists rho'.
    pose proof (i63_range t) as Ht.
    assert (Hag' : agree t rho rho') by (apply agree_ext; [slia | slia | exact Xr0]).
    assert (Et16 : to_Z (t + 16)%uint63 = to_Z t + 16).
    { rewrite Uint63.add_spec. change (to_Z 16%uint63) with 16. apply Z.mod_small. change wB with (2 ^ 63). change (to_Z two59) with (2 ^ 59) in Hn59. slia. }
    change (to_Z two59) with (2 ^ 59) in Hn59.
    pose proof Hrng as (R1 & R2 & R3 & R4 & R5). pose proof hceil_lt_2p47 as Hh47.
    assert (EL16 : forall x (k : nat), (k < 16)%nat -> to_Z x = to_Z t + Z.of_nat k -> rho' x = nth k L16 w0).
    { intros x k Hk Hx. subst rho'. apply (rho_ext_at rho t L16 x k); [subst L16; cbn; slia | exact Hx]. }
    assert (Erho't : rho' t = wa A) by (rewrite (EL16 t 0%nat); [reflexivity | slia | slia]).
    assert (Erho'e : rho' (t + 15)%uint63 = errv').
    { rewrite (EL16 _ 15%nat); [reflexivity | slia |].
      rewrite Uint63.add_spec. change (to_Z 15%uint63) with 15. change wB with (2 ^ 63). rewrite Z.mod_small by slia. slia. }
    (* [comment removed for export] *)
    assert (Hfresh : forall a k, rclient_range LB (bv_unsigned (rv rho F 2)) a k -> 0 <= k -> a + k <= A \/ A + to_Z n <= a).
    { intros a k Hr Hk. eapply (fresh_block_disjoint_client (hs_RHEAP H) (HH_RHEAP_block_range H HH) (HH_RHEAP_blocks_disjoint H HH) (HH_RHEAP_blocks_nodup H HH));
        [exact Hheap' | exact Hr | rewrite Espu; pose proof (i63_range off); slia | exact Hk]. }
    (* [comment removed for export] *)
    destruct Xnamed as [XG0in XLB0nd].
    assert (Hclient : forall a, 0 <= a < 2 ^ 64 -> client0 Q a -> ~ named_addr Q a -> rclient_range LB (bv_unsigned (rv rho F 2)) a 1).
    { intros a Ha Hcl Hna. rewrite Espu. pose proof (i63_range off).
      unfold client0, rclient_addr in Hcl. destruct Hcl as [Hs | [[Hst Hnst] | (b & Hb & Hr)]].
      - left. slia.
      - right. left. unfold ralloc_static in Hnst. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. slia.
      - destruct (in_dec bptr_eq_dec (blk_id b) (map g_id (q_G0 Q))) as [Hi|Hni].
        + exfalso. apply Hna. apply in_map_iff in Hi as (g0 & Eg & Hg0).
          pose proof (proj1 (Forall_forall _ _) XG0in g0 Hg0) as Hg0in.
          pose proof (nodup_ids_eq _ b _ XLB0nd Hb Hg0in ltac:(rewrite <- Eg; reflexivity)) as ->.
          exists g0. split; [exact Hg0|]. cbn [blk_addr RMalloc_iface_stmt.blk_size fst snd] in Hr. exact Hr.
        + right. right. exists b. split; [exact (XLB0 b Hb Hni)|]. slia. }
    assert (Hclient_addr : forall a, 0 <= a < 2 ^ 64 -> client0 Q a -> ~ named_addr Q a -> rclient_addr LB (bv_unsigned (rv rho F 2)) a).
    { intros a Ha Hcl Hna. eapply rclient_range_addr; [exact (Hclient a Ha Hcl Hna) | slia]. }
    (* [comment removed for export] *)
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ Hheap') as Hnd'. cbn [map blk_id fst] in Hnd'.
    pose proof (proj1 (NoDup_cons_iff _ _) Hnd') as [Hpfresh HndLB].
    assert (HGids : forall g, In g G -> In (g_id g) (map blk_id LB)).
    { intros g Hg. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _).
      replace (g_id g) with (blk_id (g_id g, g_addr g, to_Z (g_size g))) by reflexivity. apply in_map. exact Hin. }
    exists s', ((p, A, to_Z n) :: LB), (GB t p A n :: G).
    assert (HRn' : Rn usegs IM (t + 16)%uint63 rho'
              (FS (ret_of l) (iset 10 (FV t w_zero) (clobber clob14 (t + 1) (f_regs F)))
                  (iset 0 (err_region K (t + 15) rg0 pe) (iset t (blk_region n lg iempty) (iset 1 (drop_below off rg1) (f_mem F)))) None)
              (MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 A)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom usegs))).
    { intros rho'' Hag''.
      assert (HagF : agree t rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Et16; slia]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z t + 16 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Et16; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''t : rho'' t = wa A) by (rewrite Erho'' by slia; exact Erho't).
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))).
      { rewrite Erho'' by (change (to_Z 1%uint63) with 1; slia). subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; slia]. }
      assert (Erho''old : forall x, to_Z x < to_Z t -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by slia. subst rho'. apply rho_ext_old. exact Hx. }
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      (* [comment removed for export] *)
      assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> rclient_addr LB (bv_unsigned (rv rho F 2)) a ->
                       rview usegs m' (wa a) = rview usegs (ms_mem ms) (wa a)
                       /\ (wview usegs (ms_mem ms) (wa a) <> None -> wview usegs m' (wa a) <> None)).
      { intros a Ha Hc. destruct (Hpres a Ha Hc) as [E W]. split; [apply rview_eq_of_mem; exact E | exact W]. }
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 A)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; Z_to_bv 64 A;
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
        assert (Hnd14 : List.NoDup clob14) by (apply nodupb_spec; reflexivity).
        assert (Ht1 : to_Z (t + 1)%uint63 = to_Z t + 1).
        { rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. change wB with (2 ^ 63). slia. }
        assert (Hcl : forall k : int, iget k (clobber clob14 (t + 1) (f_regs F)) =
                      match index_of k clob14 with
                      | Some i => Some (FV (of_Z (to_Z (t + 1)%uint63 + Z.of_nat i)) w_zero)
                      | None => iget k (f_regs F) end).
        { intros k. apply iget_clobber; [exact Hnd14 | rewrite Ht1; cbn [length clob14]; slia]. }
        apply regs_match_intro. cbn [seq].
        repeat (apply Forall_cons || apply Forall_nil);
          cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ];
          match goal with |- _ = dv _ (FxState.rget ?FF ?k) =>
            let kk := eval vm_compute in k in change k with kk; rewrite (rget_regs' FF kk eq_refl) end;
          cbn [f_regs]; rewrite iget_iset;
          match goal with |- _ = dv _ match (if ?b then _ else _) with _ => _ end => let bb := eval vm_compute in b in change b with bb end;
          cbv iota.
        all: try (rewrite Hcl;
                  match goal with |- _ = dv _ match match ?ix with _ => _ end with _ => _ end =>
                    let ii := eval vm_compute in ix in change ix with ii end; cbv iota).
        all: first
          [ (* [comment removed for export] *)
            match goal with |- Z_to_bv 64 ?AA = dv ?rr (FV ?tt w_zero) => rewrite (dv_tag_zero rr tt) by slia; rewrite Erho''t; reflexivity end
          | (* [comment removed for export] *)
            match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); slia);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia);
              rewrite (EL16 (of_Z (to_Z t1 + Z.of_nat i)) (S i)); [reflexivity | slia | rewrite Etag; slia]
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
        assert (Hrg0M : iget 0%uint63 (f_mem F) = Some rg0).
        { rewrite !iget_iset in Hrg0'. change ((0 =? 1)%uint63) with false in Hrg0'.
          destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; exfalso; pose proof (f_equal to_Z Et0); change (to_Z 0%uint63) with 0 in *; slia|].
          exact Hrg0'. }
        destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0_. rewrite Hrg0M in Hrg0_. injection Hrg0_ as <-.
        destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
        (* [comment removed for export] *)
        assert (Hnewsep : forall t' rg', iget t' (f_mem F) = Some rg' ->
                  bv_unsigned (rho'' t) + to_Z n <= bv_unsigned (rho'' t') + to_Z (rg_lo rg')
                  \/ bv_unsigned (rho'' t') + to_Z (rg_len rg') <= bv_unsigned (rho'' t) + 0).
        { intros t' rg' Ht'. rewrite Erho''t, wa_unsigned by slia.
          destruct (Xdom t' rg' Ht') as [-> | [-> | Hb]].
          - rewrite Hrg0M in Ht'. injection Ht' as <-. rewrite Hrho''0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0. slia.
          - rewrite Hrg1 in Ht'. injection Ht' as <-. rewrite Erho''1, Hlo1, Hlen1. change (to_Z 0%uint63) with 0.
            pose proof (i63_range (c_stack K)). rewrite wa_unsigned by slia. slia.
          - apply in_map_iff in Hb as (g & <- & Hg).
            pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg & rgg & Hgg & Hlog & Hleng).
            rewrite Hgg in Ht'. injection Ht' as <-. rewrite Hlog, Hleng. change (to_Z 0%uint63) with 0.
            rewrite (Erho''old (g_tag g)) by slia. rewrite Hrg. pose proof (rblock_of_G H IMX K HHx Q st rho ms mo s LB G g X Hg) as (G1 & G2 & G3 & G4 & G5).
            rewrite wa_unsigned by slia.
            destruct (Hfresh (g_addr g) (to_Z (g_size g)) ltac:(right; right; exists (g_id g, g_addr g, to_Z (g_size g)); split; [exact Hin | cbn [blk_addr RMalloc_iface_stmt.blk_size fst snd]; slia]) ltac:(slia)); slia. }
        apply mem_ok_parts.
        + intros t' rg' Ht'. rewrite !iget_iset in Ht'.
          destruct (t' =? 0)%uint63 eqn:E0.
          * (* [comment removed for export] *) apply Uint63.eqb_spec in E0. subst t'. injection Ht' as <-.
            eapply (region0_part usegs IM rho'' Hrho''0 IMX eq_refl HIMX HWRX K (ms_mem ms) m' rg0 pe (t + 15)%uint63 errv'
                      (fun c => 0 <= c /\ c + 8 <= 0x358000 /\ ((exists x, In x (c_xw K) /\ to_Z x = c) \/ (exists cc, In (of_Z c, cc) (c_ro K))))).
            -- exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0M).
            -- exact Hd0.
            -- exact Hpg0.
            -- intros pn p0 ci c Hp0 Hc. pose proof (i63_range pn). pose proof (i63_range ci).
               destruct (Xinb 0%uint63 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hcb _]. rewrite Hlen0 in Hcb.
               destruct (Hc0 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hx | [He | Hr]]; [left | right; exact He | left]; (split; [slia|]; split; [clear -Hcb; slia|]); [left; exact Hx | right; exact Hr].
            -- intros c a (Hc0' & Hc8 & [(x & Hx & <-) | (cc & Hcc)]) Ha.
               ++ clear -Hkeep Hx Ha Hc0' Hc8 HK. hk_xw x Hx.
                  apply (proj1 (Hkeep a ltac:(slia) ltac:(right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; slia))).
               ++ destruct (xw_cell_ok (of_Z c)) eqn:Exw.
                  ** (* [comment removed for export] *)
                     clear -Hkeep Exw Ha Hc0' Hc8 HK. pose proof (xw_cell_ok_spec _ Exw) as Xw.
                     unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in Xw. rewrite toZ_of_Z_small in Xw by slia.
                     destruct Xw as (? & ? & ? & ? & ? & ? & ? & ?).
                     apply (proj1 (Hkeep a ltac:(slia) ltac:(right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; slia))).
                  ** pose proof (HROC _ _ _ _ _ _ Xheap Hheap' Xinv Hinv' (of_Z c) cc Hcc Exw (a - c) ltac:(slia)) as E.
                     rewrite toZ_of_Z_small in E by slia. replace (c + (a - c)) with a in E by slia. exact E.
            -- exact Hpe.
            -- exact Hinv'.
            -- rewrite EerrA in Herr'. exact Herr'.
            -- assert (Et15 : to_Z (t + 15)%uint63 = to_Z t + 15).
               { rewrite Uint63.add_spec. change (to_Z 15%uint63) with 15. change wB with (2 ^ 63). apply Z.mod_small. slia. }
               rewrite dv_tag_zero by (rewrite Et15; slia). rewrite Erho'' by (rewrite Et15; slia). exact Erho'e.
            -- exact Eerr8.
            -- exact Ebi.
            -- destruct (err_page_ok_inv _ _ Hep) as (rg0b & pb & Hrg0b & Hir & _). fold F in Hrg0b. rewrite Hrg0M in Hrg0b. injection Hrg0b as <-.
               unfold in_region in Hir. rewrite !andb_true_iff in Hir. destruct Hir as [[[Hob _] _] Hir]. apply Uint63.leb_spec in Hir.
               apply Uint63.ltb_spec in Hob. change (to_Z off_bound) with (2 ^ 62) in Hob.
               rewrite Uint63.add_spec in Hir. change (to_Z 8%uint63) with 8 in Hir. change wB with (2 ^ 63) in Hir.
               pose proof (i63_range (rg_len rg0)). rewrite Z.mod_small in Hir by slia. exact Hir.
            -- rewrite Hlen0. reflexivity.
          * destruct (t' =? t)%uint63 eqn:Et'.
            -- (* [comment removed for export] *) apply Uint63.eqb_spec in Et'. subst t'. injection Ht' as <-.
               apply (blk_region_part usegs IM rho'' m' t n lg A Erho''t).
               ++ intros E. pose proof (f_equal to_Z E). change (to_Z 0%uint63) with 0 in *. slia.
               ++ slia.
               ++ exact Hrng.
               ++ replace (2 ^ to_Z lg) with (to_Z al) by (destruct Hal as [[-> ->] | [[-> ->] | [-> ->]]]; reflexivity). exact HAal.
               ++ slia.
               ++ slia.
               ++ destruct Hblk as [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by slia. exact Hw.
            -- destruct (t' =? 1)%uint63 eqn:E1.
               ++ (* [comment removed for export] *) apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
                  destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
                  apply (stack_part usegs IM rho'' (ms_mem ms) m' rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q)).
                  ** exact Erho''1.
                  ** exact Hlo1.
                  ** exact Hd1.
                  ** exact Hkd1.
                  ** rewrite Hlen1. reflexivity.
                  ** rewrite Hlen1. pose proof (i63_range off). slia.
                  ** Z.div_mod_to_equations. slia.
                  ** exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1).
                  ** exact Xstk.
                  ** pose proof hceil_pos. slia.
                  ** rewrite <- Espu. exact Hstk'.
                  ** intros a Ha. destruct Xstk as (_ & H64 & _). apply Hkeep; [slia | left; rewrite Espu; slia].
               ++ (* [comment removed for export] *)
                  destruct (Xdom t' rg' Ht') as [E | [E | Hb]]; [subst t'; rewrite Uint63.eqb_refl in E0; discriminate | subst t'; rewrite Uint63.eqb_refl in E1; discriminate |].
                  apply in_map_iff in Hb as (g & <- & Hg).
                  pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg & rgg & Hgg & Hlog & Hleng).
                  rewrite Hgg in Ht'. injection Ht' as <-.
                  pose proof (rblock_of_G H IMX K HHx Q st rho ms mo s LB G g X Hg) as (G1 & G2 & G3 & G4 & G5).
                  apply (mem_part_transfer usegs IM rho'' (ms_mem ms) m' (g_tag g) rgg (g_addr g)).
                  ** rewrite (Erho''old (g_tag g)) by slia. exact Hrg.
                  ** slia.
                  ** rewrite Hleng. slia.
                  ** intros a Ha. rewrite Hlog, Hleng in Ha. change (to_Z 0%uint63) with 0 in Ha.
                     apply Hkeep; [slia|]. right. right. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr RMalloc_iface_stmt.blk_size fst snd]; slia].
                  ** intros pn sg _ E. pose proof (f_equal to_Z E). change (to_Z 0%uint63) with 0 in *. slia.
                  ** exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hgg).
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2. rewrite !iget_iset in Hi1, Hi2.
          assert (Hold : forall t' rg', t' <> t ->
                    (if (t' =? 0)%uint63 then Some (err_region K (t + 15) rg0 pe)
                     else if (t' =? t)%uint63 then Some (blk_region n lg iempty)
                     else if (t' =? 1)%uint63 then Some (drop_below off rg1) else iget t' (f_mem F)) = Some rg' ->
                    exists rg, iget t' (f_mem F) = Some rg /\ rg_lo rg = rg_lo rg' /\ rg_len rg = rg_len rg').
          { intros t' rg' Hne' Ht'.
            destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; subst t'; injection Ht' as <-; exists rg0; split; [exact Hrg0M | split; reflexivity]|].
            destruct (t' =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; congruence|].
            destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; subst t'; injection Ht' as <-; exists rg1; split; [exact Hrg1 | split; reflexivity]|].
            exists rg'. split; [exact Ht' | split; reflexivity]. }
          destruct (Z.eq_dec (to_Z t1) (to_Z t)) as [E1t|E1t].
          * apply to_Z_inj in E1t. subst t1.
            rewrite (eqb_neq_false t 0%uint63) in Hi1 by (intros E; pose proof (f_equal to_Z E); change (to_Z 0%uint63) with 0 in *; slia).
            rewrite Uint63.eqb_refl in Hi1. cbv iota in Hi1. injection Hi1 as <-. cbn [rg_len rg_lo blk_region]. change (to_Z 0%uint63) with 0.
            destruct (Hold t2 r2 ltac:(intros E; apply Hne; symmetry; exact E) Hi2) as (rg & Hrg2 & El & En). rewrite <- El, <- En.
            exact (Hnewsep t2 rg Hrg2).
          * assert (Hne1 : t1 <> t) by (intros E; apply E1t; rewrite E; reflexivity).
            destruct (Z.eq_dec (to_Z t2) (to_Z t)) as [E2t|E2t].
            -- apply to_Z_inj in E2t. subst t2.
               rewrite (eqb_neq_false t 0%uint63) in Hi2 by (intros E; pose proof (f_equal to_Z E); change (to_Z 0%uint63) with 0 in *; slia).
               rewrite Uint63.eqb_refl in Hi2. cbv iota in Hi2. injection Hi2 as <-. cbn [rg_len rg_lo blk_region]. change (to_Z 0%uint63) with 0.
               destruct (Hold t1 r1 Hne1 Hi1) as (rg & Hrg1' & El & En). rewrite <- El, <- En.
               destruct (Hnewsep t1 rg Hrg1'); [right | left]; assumption.
            -- assert (Hne2 : t2 <> t) by (intros E; apply E2t; rewrite E; reflexivity).
               destruct (Hold t1 r1 Hne1 Hi1) as (q1 & Hq1 & El1 & En1). destruct (Hold t2 r2 Hne2 Hi2) as (q2 & Hq2 & El2 & En2).
               rewrite <- El1, <- En1, <- El2, <- En2. exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
    constructor; cbn [i_F i_n i_blk i_cost i_cnt i_big f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS].
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; slia].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; slia].
    - eapply agree_trans; [exact Xag | exact Hag' | slia].
    - rewrite Et16. slia.
    - exact Hheap'.
    - exact Hkrel'.
    - exact (mpres_trans H HH _ _ _ Xmp Hmpres').
    - cbn [map g_tag g_size]. rewrite XG. reflexivity.
    - (* [comment removed for export] *) constructor.
      + cbn [g_id g_addr g_size g_tag]. split; [left; reflexivity|]. split; [exact Erho't|]. split; [slia|].
        split; [rewrite Et16; slia|].
        exists (blk_region n lg iempty). rewrite iget_iset. replace (t =? 0)%uint63 with false.
        2:{ symmetry. destruct (t =? 0)%uint63 eqn:E; [apply Uint63.eqb_spec in E; exfalso; subst t; rewrite E in Hn2; change (to_Z 0%uint63) with 0 in Hn2; slia | reflexivity]. }
        rewrite iget_iset_same. split; [reflexivity|]. split; reflexivity.
      + apply Forall_forall. intros g Hg.
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg & rgg & Hgg & Hlog & Hleng).
        split; [right; exact Hin|]. split; [subst rho'; rewrite rho_ext_old by slia; exact Hrg|]. split; [exact Hsz|].
        split; [rewrite Et16; slia|].
        exists rgg. rewrite !iget_iset.
        destruct (g_tag g =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); change (to_Z 0%uint63) with 0 in *; slia|].
        destruct (g_tag g =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; exfalso; pose proof (f_equal to_Z Et'); slia|].
        destruct (g_tag g =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); change (to_Z 1%uint63) with 1 in *; slia|].
        split; [exact Hgg|]. split; assumption.
    - (* [comment removed for export] *) cbn [map g_id]. constructor; [|exact XGnd]. intros Hin. apply Hpfresh.
      apply in_map_iff in Hin as (g & <- & Hg). exact (HGids g Hg).
    - (* [comment removed for export] *) cbn [map g_tag]. constructor; [|exact XGtnd]. intros Hin.
      apply in_map_iff in Hin as (g & E & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & Htg & _).
      rewrite E in Htg. slia.
    - (* [comment removed for export] *) constructor.
      + right. cbn [g_addr g_size g_id]. split.
        * intros a Hcl Hna Hin.
          assert (Ha64 : 0 <= a < 2 ^ 64) by slia.
          destruct (Hfresh a 1 (Hclient a Ha64 Hcl Hna) ltac:(slia)); slia.
        * intros b Hb Hni E. apply Hpfresh. rewrite E. apply in_map. exact (XLB0 b Hb Hni).
      + exact XGnew.
    - (* [comment removed for export] *) constructor.
      + cbn [g_addr g_size]. pose proof (stk_of_rw_cells usegs m' A _ Hblk) as Hs. cbn [cells_size csize] in Hs.
        rewrite Nat.add_0_r, Z2Nat.id in Hs by slia. exact Hs.
      + apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _ & Hsz & _).
        pose proof (rblock_of_G H IMX K HHx Q st rho ms mo s LB G g X Hg) as (G1 & G2 & G3 & G4 & G5).
        apply (stk_pres usegs (ms_mem ms)); [exact Hs|]. intros a Ha. apply Hpres; [slia|].
        right. right. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr RMalloc_iface_stmt.blk_size fst snd]; slia].
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; left; exact E0|].
      destruct (t' =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; right; right; left; symmetry; exact Et'|].
      destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; right; left; exact E1|].
      destruct (Xdom t' rg' Ht') as [H0' | [H1' | Hb']]; [left; exact H0' | right; left; exact H1' | right; right; right; exact Hb'].
    - (* [comment removed for export] *) destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0).
      assert (Erg0 : rg0 = rg0_).
      { rewrite !iget_iset in Hrg0'. change ((0 =? 1)%uint63) with false in Hrg0'.
        destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; exfalso; pose proof (f_equal to_Z Et0); change (to_Z 0%uint63) with 0 in *; slia|].
        cbv iota in Hrg0'. congruence. }
      subst rg0_.
      exists (err_region K (t + 15) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len rg_dflt rg_pages]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0|].
      intros pn p' Hp'. rewrite iget_iset in Hp'. destruct (pn =? c_errcell K >> 12)%uint63 eqn:Epn.
      + apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_kind]. exact (Hpg0 _ _ Hpe).
      + exact (Hpg0 _ _ Hp').
    - (* [comment removed for export] *) destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
      exists (drop_below off rg1). rewrite !iget_iset. change ((1 =? 0)%uint63) with false.
      destruct (1 =? t)%uint63 eqn:Et1; [apply Uint63.eqb_spec in Et1; exfalso; pose proof (f_equal to_Z Et1); change (to_Z 1%uint63) with 1 in *; slia|].
      change ((1 =? 1)%uint63) with true. cbv iota. split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt]. repeat split; assumption.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc).
      assert (rg0_ = rg0).
      { rewrite !iget_iset in Hrg0'. change ((0 =? 1)%uint63) with false in Hrg0'.
        destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; exfalso; pose proof (f_equal to_Z Et0); change (to_Z 0%uint63) with 0 in *; slia|].
        cbv iota in Hrg0'. fold F in Hrg0_. congruence. }
      subst rg0_. exists (err_region K (t + 15) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len]. exact Hroc.
    - (* [comment removed for export] *) intros t' rg' pn p' ci c Ht' Hp' Hc. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0.
      + injection Ht' as <-. unfold err_region in Hp' |- *. cbn [rg_pages rg_len] in Hp' |- *.
        assert (Hrg0M : iget 0%uint63 (f_mem F) = Some rg0).
        { rewrite !iget_iset in Hrg0'. change ((0 =? 1)%uint63) with false in Hrg0'.
          destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; exfalso; pose proof (f_equal to_Z Et0); change (to_Z 0%uint63) with 0 in *; slia|].
          exact Hrg0'. }
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
      + destruct (t' =? t)%uint63 eqn:Et'.
        * injection Ht' as <-. unfold blk_region in Hp'. cbn [rg_pages] in Hp'. rewrite iget_iempty in Hp'. discriminate.
        * destruct (t' =? 1)%uint63 eqn:E1.
          -- injection Ht' as <-. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
             unfold drop_below. cbn [rg_len].
             unfold drop_page in Hc. cbn [fst snd] in Hc.
             destruct (pn =? off >> 12)%uint63.
             ++ cbn [pg_cells] in Hc. destruct (keep_cells_ge_inv _ _ _ _ Hc) as [_ Hc']. fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc').
             ++ fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc).
          -- exact (Xinb t' rg' pn p' ci c Ht' Hp' Hc).
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|].
      destruct (t' =? t)%uint63 eqn:Et'.
      + injection Ht' as <-. unfold blk_region. cbn [rg_dflt rg_pages]. split; [reflexivity|]. intros pn p' Hp'. rewrite iget_iempty in Hp'. discriminate.
      + destruct (t' =? 1)%uint63 eqn:E1.
        * injection Ht' as <-. apply Uint63.eqb_spec in E1. subst t'. fold F in Hrg1. destruct (Xkinds 1%uint63 rg1 Hrg1 Ht'0) as [Hdu1 Hku1].
          unfold drop_below. cbn [rg_dflt rg_pages]. split; [exact Hdu1|].
          intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
          unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hku1 _ _ Hp0).
        * exact (Xkinds t' rg' Ht' Ht'0).
    - (* [comment removed for export] *) cbn [lb_bytes fold_right RMalloc_iface_stmt.blk_size snd]. fold (lb_bytes LB). rewrite Ecost. slia.
    - (* [comment removed for export] *) cbn [length]. rewrite Ecnt. slia.
    - (* [comment removed for export] *) rewrite lb_big_cons. cbn [RMalloc_iface_stmt.blk_size snd]. rewrite Ebig, Hbig1.
      assert (HeapSR_iface.big1 (to_Z n) <= HeapSR_iface.big1 (to_Z n + to_Z al)).
      { unfold HeapSR_iface.big1, HeapSR_iface.BIGB. destruct (Z.ltb_spec 2028 (to_Z n)); destruct (Z.ltb_spec 2028 (to_Z n + to_Z al)); slia. }
      rewrite Hbig1al in *. slia.
    - (* [comment removed for export] *) apply (stk_merge usegs m' (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q)); [exact Hstk' | | rewrite Espu; pose proof (i63_range off); slia].
      apply (stk_pres usegs (ms_mem ms)); [exact Hstk_hi|]. intros a Ha. apply Hpres; [|left; slia].
      destruct Hstk_hi as (_ & Hhi64 & _). rewrite Espu in Ha. pose proof (i63_range off). slia.
    - repeat split; assumption.
    - exact Haux'.
    - exact Hinv'.
    - rewrite EerrA in Herr'. pose proof (stk_of_rw_cells usegs m' (errA K) [C4 errv'] Herr') as Hs. cbn [cells_size csize] in Hs.
      replace (errA K + Z.of_nat 4) with (errA K + 4) in Hs by slia. exact Hs.
    - intros b Hb Hni. right. exact (XLB0 b Hb Hni).
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - (* [comment removed for export] *) intros b [<- | Hb].
      + right. exists (GB t p A n). split; [left; reflexivity | reflexivity].
      + destruct (XLBsub b Hb) as [Hb0 | (g & Hg & ->)]; [left; exact Hb0 | right; exists g; split; [right; exact Hg | reflexivity]].
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne).
      apply Hpres; [exact Ha | exact (Hclient_addr a Ha Hcl Hna)].
  Qed.
End NodeA.
