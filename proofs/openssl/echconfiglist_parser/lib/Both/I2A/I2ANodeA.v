(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0 SecLazy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit I2ANodeM I2ANodeSig I2ANodeS I2AFill I2ANodeX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia0 := Zify.zify; xlia zchecker.
Ltac slia :=
  repeat match goal with
         | HB : @eq bool _ _ |- _ => clear HB
         | HB : _ = Z.min _ _ |- _ => clear HB
         | HB : context [to_Z (Uint63.add _ _)] |- _ => clear HB
         | HB : context [to_Z (Uint63.sub _ _)] |- _ => clear HB
         end;
  Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox H := unfold boxed in H.
(* [comment removed for export] *)
Definition alg (x c : Z) : Prop := x mod c = 0.
Ltac hmod H := lazymatch type of H with ?x mod ?c = 0 => change (alg x c) in H end.
Ltac smod H := unfold alg in H.

Section NodeA.
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
  Hypothesis HROC : ro_const A.
  (* [comment removed for export] *)
  Hypothesis MAL : memalign_stmt H (to_Z (ka_memalign A)) (to_Z (ka_pc0a A)).
  Let HH : asan_rt_hyps H := proj1 HHx.

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

  Lemma log2_al_inv : forall al lg, log2_al al = Some lg -> 2 ^ to_Z lg = to_Z al /\ (to_Z al = 16 \/ to_Z al = 32 \/ to_Z al = 64) /\ 4 <= to_Z lg <= 6.
  Proof.
    intros al lg Hl. unfold log2_al in Hl.
    destruct (al =? 16)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; injection Hl as <-; subst al; cbn; slia0|].
    destruct (al =? 32)%uint63 eqn:E2; [apply Uint63.eqb_spec in E2; injection Hl as <-; subst al; cbn; slia0|].
    destruct (al =? 64)%uint63 eqn:E3; [apply Uint63.eqb_spec in E3; injection Hl as <-; subst al; cbn; slia0| discriminate Hl].
  Qed.

  Lemma rw_c8_of_cb8 : forall m a bs, length bs = 8%nat ->
    rw_cells asegs m a [Cells.CB 8 bs] -> rw_cells asegs m a [C8 (le_bytes_to_word bs)].
  Proof.
    intros m a bs Hlen [[Hwf Hb] Hw]. split; [split|].
    - cbn. split; exact I.
    - cbn [cells_bytes cbytes] in Hb |- *. rewrite app_nil_r in Hb |- *. unfold le8, word_to_le_bytes, le_bytes_to_word.
      rewrite Z_to_bv_unsigned.
      assert (Hnn : 0 <= bytes_le_to_Z bs < 2 ^ 64).
      { pose proof (bytes_le_to_Z_bound bs) as E. rewrite Hlen in E. exact E. }
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by slia0.
      replace 8%nat with (length bs) at 1 by exact Hlen. rewrite Z_to_le_bytes_of_bytes. exact Hb.
    - exact Hw.
  Qed.
  Lemma rw_c8_of_stk : forall m a, stk asegs m a (a + 8) -> exists v, rw_cells asegs m a [C8 v].
  Proof.
    intros m a Hs. destruct (stk_carve asegs m a (a + 8) 8 Hs ltac:(slia0)) as [_ (junk & Hrw)].
    replace (a + 8 - Z.of_nat 8) with a in Hrw by slia0.
    pose proof Hrw as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hlen _].
    exists (le_bytes_to_word junk). apply rw_c8_of_cb8; [exact Hlen | exact Hrw].
  Qed.

  Theorem anode_memalign_sound : anode_memalign_sig H IMX A.
  Proof.
    unfold anode_memalign_sig, anode_concl.
    intros Q st st' rho msF mo Hnode Hpc Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_memalign in Hnode.
    destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (ptr_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) 8) as [[tm offm]|] eqn:Hpa; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) 11)) as [al|] eqn:Ha1; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) 12)) as [n|] eqn:Ha2; [|discriminate].
    destruct (log2_al al) as [lg|] eqn:Hlg; [|discriminate].
    destruct (pop_cost 3 al n (a_cs st)) as [cs|] eqn:Hpop; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hguard; [|discriminate] end.
    destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
    destruct (write_cell M1 tm offm (FV (a_n st) w_zero)) as [M1'|] eqn:HWC; [|discriminate].
    destruct (set_errno K (a_n st + 16)%uint63 (iset (a_n st + 1)%uint63 (sh_region false (a_n st) n) (iset (a_n st) (blk_region n lg iempty) M1'))) as [M2|] eqn:HM2; [|discriminate].
    injection Hnode as <-.
    destruct (call_okn_inv A _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv A _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv. pose proof (conc63_inv _ _ Ha1) as Ea1. pose proof (conc63_inv _ _ Ha2) as Ea2.
    pose proof (pop_cost_inv _ _ _ _ _ Hpop) as Ecs.
    rewrite !andb_true_iff in Hguard. destruct Hguard as [[[[[[[[[[[[Hn1 Hn32] Hal8] Hc0'] Hal64] Hn32k] Hc1] Hc2] Hk1] Hk2] Hlocm] Hchain] Hrook].
    apply Uint63.eqb_spec in Hal64. apply (f_equal to_Z) in Hal64. change (to_Z 64%uint63) with 64 in Hal64. apply Uint63.eqb_spec in Hn32k. apply (f_equal to_Z) in Hn32k. change (to_Z 32768%uint63) with 32768 in Hn32k.
    apply Uint63.leb_spec in Hn1. apply Uint63.leb_spec in Hn32. change (to_Z 1%uint63) with 1 in Hn1. change (to_Z 32768%uint63) with 32768 in Hn32.
    apply Uint63.eqb_spec in Hal8. apply (f_equal to_Z) in Hal8. rewrite to_Z_land7 in Hal8. change (to_Z 0%uint63) with 0 in Hal8.
    apply Uint63.leb_spec in Hc0'. apply Uint63.leb_spec in Hc1. apply Uint63.leb_spec in Hc2.
    apply Uint63.leb_spec in Hk1. apply Uint63.leb_spec in Hk2.
    destruct (log2_al_inv _ _ Hlg) as (Elg & Hal & Hlg46).
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    destruct (ptr_arg_inv _ _ _ _ _ Hpa) as (Ea0 & Htm0 & rgm & Hrgm & Hlom & Hom & Hnlm). change (to_Z 8%uint63) with 8 in Hom, Hnlm.
    destruct (set_errno_inv _ _ _ _ HM2) as (rg0 & pe & Hrg0' & Hpe & Hpew & ->).
    rewrite !iget_iset in Hrg0'.
    (* [comment removed for export] *)
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe XFFstk].
    set (F := a_F st) in *. set (t := a_n st) in *.
    destruct (write_cell_inv _ _ _ _ _ HWC) as (rgm1 & Hrgm1 & PGWRm & EM1').
    set (rgW := wb_region rgm1 (offm >> 12) (wc_page (wb_cur rgm1 (offm >> 12)) ((offm land 4095) >> 3) (FV t w_zero))) in EM1'. subst M1'.
    assert (Hag : agree t rho rho) by (apply agree_refl; exact Xr0).
    pose proof (XRn rho Hag) as HR. pose proof (R_mem _ _ _ _ _ HR) as Hmem. cbn [f_mem] in Hmem. fold F in Hmem.
    pose proof (canonR_R asegs IM rho F ms HR Xcan) as Ems.
    rewrite Xfr, Xfc, Xrom, Eresv in Ems. cbn [option_map] in Ems.
    replace (f_pc F) with (f_pc (a_F st)) in Ems by reflexivity. rewrite Hpc in Ems.
    assert (Erv : forall k, rv rho F k = dv rho (FxState.rget F (of_Z k))) by (intros; reflexivity).
    hk_err. acb. unfold AFS_STACK, AINTRIN_STACK, AMALLOC_STACK, AREALLOC_STACK, AFREE_STACK in *. pose proof (i63_range (c_stack K)) as Hcs.
    destruct Xlo as (Hhl & Hlsp & HspB & Hsp16 & Hsp32 & HB64 & Hshi). pose proof (i63_range off) as Hoff.
    pose proof (i63_range t) as Ht. change (to_Z two59) with (2 ^ 59) in Hn59. destruct Xn0 as [Xn0a Xn0b].
    pose proof (i63_range n) as Hn. pose proof (i63_range al) as Hal0. pose proof (i63_range offm) as Hom0. pose proof (i63_range tm) as Htm.
    assert (Esp : rv rho F 2 = adr rho 1%uint63 (to_Z off)).
    { rewrite Erv. change (of_Z 2) with 2%uint63. fold F in Esp2. rewrite Esp2. apply dv_adr; [cbn; slia | reflexivity]. }
    assert (Espu : bv_unsigned (rv rho F 2) = q_sp0 Q - to_Z (c_stack K) + to_Z off).
    { rewrite Esp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); clear - Hhl Hlsp HspB HB64 Hcs Hoff Hoff2 ACEILB; slia. }
    assert (Etpv : rv rho F 4 = Z_to_bv 64 ATP).
    { rewrite Erv. change (of_Z 4) with 4%uint63. fold F in Etp. rewrite Etp, (dv_conc63 rho _ Xr0). f_equal. exact Etp0. }
    assert (Ea1v : rv rho F 11 = Z_to_bv 64 (to_Z al)).
    { rewrite Erv. change (of_Z 11) with 11%uint63. fold F in Ea1. rewrite Ea1. apply dv_conc63. exact Xr0. }
    assert (Ea2v : rv rho F 12 = Z_to_bv 64 (to_Z n)).
    { rewrite Erv. change (of_Z 12) with 12%uint63. fold F in Ea2. rewrite Ea2. apply dv_conc63. exact Xr0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    (* [comment removed for export] *)
    destruct (rw_c4_of_stk asegs _ _ Xerr) as [errv Herrv].
    assert (EerrA : bv_unsigned (rv rho F 4) + -164 = errA A).
    { rewrite Etpv. unfold errA. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      unfold ATP. rewrite Z.mod_small by (clear; slia). unfold AERRNO, ATP in Eerr. clear - Eerr. slia. }
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q) Xstk ltac:(rewrite Espu; clear - Hhl Hlsp Hoff Hoff2; slia)) as [Hstk_lo Hstk_hi].
    destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0_.
    destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. assert (Erg1 : rg1_ = rg1) by (clear - Hrg1 Hrg1_; congruence). subst rg1_.
    pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
    pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
    (* [comment removed for export] *)
    pose proof (i63_range (a_cost st)) as Hcost0. pose proof (i63_range (c_cost K)) as Hccost. pose proof (i63_range (a_cnt st)) as Hcnt0. pose proof (i63_range (c_cnt K)) as Hccnt.
    destruct (HK_caps A HK) as (Hcap1 & Hcap2 & Hcap3).
    assert (Ecost : to_Z (a_cost st + n)%uint63 = to_Z (a_cost st) + to_Z n) by (rewrite to_Z_add_small; [reflexivity| clear - Hcost0 Hn Hc2 Hccost Hcap1 Hn32 Hn1; slia0]).
    assert (Ecost2 : to_Z (a_cost st + n + al)%uint63 = to_Z (a_cost st) + to_Z n + to_Z al) by (rewrite to_Z_add_small, Ecost; [reflexivity| rewrite Ecost; clear - Hcost0 Hn Hc2 Hccost Hcap1 Hn32 Hn1 Hal; slia0]).
    assert (Ecnt : to_Z (a_cnt st + 1)%uint63 = to_Z (a_cnt st) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; [reflexivity| clear - Hcnt0 Hk2 Hccnt Hcap2; slia0]).
    rewrite Ecost2 in Hc1. rewrite Ecnt in Hk1.
    assert (Halloc : as_alloc_ok H s LB (to_Z n + to_Z al)).
    { apply (ah_alloc H HH s LB (ms_mem ms) (to_Z n + to_Z al) Xheap); clear - Xcost Xcnt Hc1 Hk1 Hn1 Hal; slia. }
    clear Hal. box Elg.
    (* [comment removed for export] *)
    destruct XAL as (done & Ecsq & HAL).
    assert (HCm : as_Cm H (to_Z n + to_Z al) <= as_AL H s /\ as_AL H s - as_Cm H (to_Z n + to_Z al) >= q_AL0 Q - csum H (done ++ [(3%uint63, al, n)])).
    { rewrite Ecs in Ecsq. pose proof XAL0 as B0. rewrite Ecsq, csum_app in B0. cbn [csum fold_right] in B0. fold (csum H cs) in B0.
      unfold cost1 in B0. change ((3 =? 0)%uint63) with false in B0. change ((3 =? 1)%uint63) with false in B0. change ((3 =? 2)%uint63) with false in B0. cbv iota in B0.
      pose proof (csum_nonneg H HHx cs) as CN. rewrite csum_app. cbn [csum fold_right]. unfold cost1.
      change ((3 =? 0)%uint63) with false. change ((3 =? 1)%uint63) with false. change ((3 =? 2)%uint63) with false. cbv iota.
      replace (to_Z n + to_Z al) with (to_Z al + to_Z n) by (clear; slia0). clear - B0 CN HAL. slia. }
    destruct HCm as [HCm HAL'].
    (* [comment removed for export] *)
    destruct (chain_okb_trace H IMX A HK HHx Hpfc _ _ _ _ _ _ _ _ _ _ _ _ _ X Hchain) as (CH & Hch & Htr).
    assert (Hral : bv_unsigned (rv rho F 1) = to_Z l).
    { rewrite Erav, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). pose proof (i63_range l). apply Z.mod_small. slia. }
    rewrite <- Hral in Htr.
    assert (Hch8 : as_chain H (ms_mem ms) (bv_unsigned (rv rho F 8)) CH) by exact Hch.
    (* [comment removed for export] *)
    fold F in Hlocm, Hrgm, Ea0.
    assert (OLDLT : forall x rg, iget x (f_mem F) = Some rg -> to_Z x < to_Z t).
    { intros x rg Hx. destruct (Xdom x rg Hx) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl']]]]]]]];
        [change (to_Z 0%uint63) with 0; clear - Xn0a Xn0b; slia| change (to_Z 1%uint63) with 1; clear - Xn0a Xn0b; slia
        | change (to_Z 2%uint63) with 2; clear - Xn0a Xn0b; slia| change (to_Z 3%uint63) with 3; clear - Xn0a Xn0b; slia| ..].
      - apply in_map_iff in Hb as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hbs as (g & <- & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _). pose proof (i63_range (g_tag g)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hf as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). clear - Htg2. slia.
      - apply in_map_iff in Hfs as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 1%uint63) with 1; clear - Htg2 H0 Hn59; slia0). change (to_Z 1%uint63) with 1. clear - Htg2. slia.
      - apply in_map_iff in Hfl' as (f & <- & Hf). pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Htg2 & _). pose proof (i63_range (f_tag f)).
        rewrite to_Z_add_small by (change (to_Z 2%uint63) with 2; clear - Htg2 H0 Hn59; slia0). change (to_Z 2%uint63) with 2. clear - Htg2. slia. }
    assert (Htm_lt : to_Z tm < to_Z t) by exact (OLDLT tm rgm Hrgm).
    assert (Ea0v : rv rho F 10 = adr rho tm (to_Z offm)).
    { rewrite Erv. change (of_Z 10) with 10%uint63. rewrite Ea0. apply dv_adr; [clear - Htm_lt Hn59; slia0| reflexivity]. }
    destruct (range_objW H IMX A HK HHx Q st rho msF mo s LB G FF XS ms false tm offm 8%uint63 off rgm X Esp2 ltac:(clear - Hoff1 Em1 Ef2; slia) Hoff2 Hn59 Htm0 Hrgm Hlom Hom Hnlm ltac:(change (to_Z 8%uint63) with 8; clear; slia0) Hlocm)
      as (Dm & (ErDm & HDm0 & HDm8 & HDmtop & Hlodm & Hdfdm & Hkddm & RNGm & HDmhi & STKm & OBJFm & (SHVm & IAMm & ACOm & CWDm & S0Dm & AFDm & LODm & SP0Dm & EXDm)) & SRDm).
    fold F t in STKm, OBJFm, EXDm |- *. change (to_Z 8%uint63) with 8 in *. rewrite <- ?Espu in STKm, LODm.
    box STKm. box OBJFm. box LODm.
    set (P := Dm + to_Z offm) in *.
    pose proof (proj1 (proj1 Hmem tm rgm Hrgm)) as (_ & Hlenm62 & _). pose proof (i63_range (rg_len rgm)) as Hldm.
    assert (EPv : rv rho F 10 = wa P) by (rewrite Ea0v; subst P; apply (adr_eq_wa rho); [exact ErDm| exact HDm0| clear - Hom0; slia0| clear - RNGm HDmhi Hom0; unfold AAPP_HI in HDmhi; slia0]).
    assert (EPu : bv_unsigned (rv rho F 10) = P) by (rewrite EPv; apply wa_unsigned; clear - HDm0 RNGm HDmhi Hom0; unfold AAPP_HI in HDmhi; slia0).
    assert (HP8 : P mod 8 = 0) by (subst P; clear - HDm8 Hal8 Hom0 HDm0; Z.div_mod_to_equations; slia0).
    hmod HP8. hmod HDm8. hmod Hal8.
    destruct (rw_c8_of_stk (ms_mem ms) P (SRDm (P + 8) ltac:(clear - RNGm; subst P; slia))) as [pjunk RWP].
    (* [comment removed for export] *)
    pose proof MAL as MS0. unfold memalign_stmt in MS0.
    eapply (ah_mono H HH).
    { eapply (MS0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q_F Q) (q_fc Q) msF (ms_mem ms) s LB P (to_Z al) (to_Z n) (q_lo Q) (q_B Q) errv mo CH pjunk).
      - rewrite <- Ems. exact Xvis.
      - exact Xheap.
      - exact Xak.
      - exact Halloc.
      - exact HCm.
      - exact Xaux.
      - clear - Espu HspB Hoff2; slia.
      - exact Hstk_lo.
      - exact SB1.
      - unfold AMALLOC_STACK. clear - Espu Hlsp Hoff1 Em1; slia.
      - rewrite EerrA. exact Herrv.
      - exact Xinv.
      - exact Etpv.
      - clear - Espu Hoff16 Hsp32 Hsp16 Hcs Hoff Est16. Z.div_mod_to_equations. slia.
      - exact Xac.
      - exact Hch8.
      - exact Htr.
      - exact EPv.
      - exact HP8.
      - exact RWP.
      - exact CWDm.
      - exact ACOm.
      - exact LODm.
      - exact Ea1v.
      - exact Hal64.
      - exact Ea2v.
      - exact Hn32k. }
    (* [comment removed for export] *)
    intros [msF' mo'] Hpost. unfold memalign_post in Hpost. cbn [cfg_ms cfg_model] in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ab & junk & p & s'
                       & Evis' & Hak' & Hmpres' & Hinv' & Hstk' & Herr' & Haux' & Hpres & Hrng & HAal & Hheap' & Hblk & Had & HPcell & Hac' & HALs').
    lazymatch type of HAal with ?x mod ?c = 0 => change (alg x c) in HAal end.
    cbn [cfg_ms cfg_model].
    set (L17 := [wa Ab; wa (sh Ab); t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6'; errv']).
    set (rho' := rho_ext rho t L17).
    exists rho'.
    assert (Hag' : agree t rho rho') by (apply agree_ext; [slia0 | slia0 | exact Xr0]).
    assert (Et17 : to_Z (t + 17)%uint63 = to_Z t + 17) by (rewrite to_Z_add_small; change (to_Z 17%uint63) with 17; slia0).
    assert (Et16 : to_Z (t + 16)%uint63 = to_Z t + 16) by (rewrite to_Z_add_small; change (to_Z 16%uint63) with 16; slia0).
    assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia0).
    assert (Et2 : to_Z (t + 2)%uint63 = to_Z t + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia0).
    assert (Htms : (tm =? t + 1)%uint63 = false) by (destruct (tm =? t + 1)%uint63 eqn:E; [apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; rewrite Et1 in E; exfalso; clear - E Htm_lt; slia0| reflexivity]).
    pose proof Hrng as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    (* [comment removed for export] *)
    hmod Hoff16. hmod Hl2. hmod Eerr8. hmod Est16. hmod F3. hmod Hsp16. hmod Hsp32. hmod R2. clear Hrng.
    rename ACEILB into ACEILM0. pose proof ACEILM0 as (ACEIL1 & ACEILM & ACEIL2).
    assert (ACEILB : 140735332483072 <= aceil <= 140737479966720 /\ aceil <= hceil < aceil + 4096) by (clear - ACEIL1 ACEIL2; slia0).
    clear ACEILM0 ACEIL1 ACEIL2. hmod ACEILM.
    assert (EL17 : forall x (k : nat), (k < 17)%nat -> to_Z x = to_Z t + Z.of_nat k -> rho' x = nth k L17 w0).
    { intros x k Hk Hx. subst rho'. apply (rho_ext_at rho t L17 x k); [subst L17; cbn; slia0 | exact Hx]. }
    assert (Erho't : rho' t = wa Ab) by (rewrite (EL17 t 0%nat); [reflexivity | slia0 | slia0]).
    assert (Erho's : rho' (t + 1)%uint63 = wa (sh Ab)) by (rewrite (EL17 _ 1%nat); [reflexivity | slia0 | rewrite Et1; slia0]).
    assert (Erho'e : rho' (t + 16)%uint63 = errv') by (rewrite (EL17 _ 16%nat); [reflexivity | slia0 | rewrite Et16; slia0]).
    (* [comment removed for export] *)
    assert (Hfresh : forall a k, aclient_range H LB (bv_unsigned (rv rho F 2)) a k -> 0 < k -> a + k <= Ab \/ Ab + to_Z n <= a).
    { intros a k Hr Hk. eapply (new_block_apart H HHx); [exact Hheap' | exact Hr | rewrite Espu; clear - SB1 Hhl Hlsp Hoff Hoff2 Hcs HB64; slia0 | exact Hk]. }
    assert (HfreshS : forall a k, aclient_range H LB (bv_unsigned (rv rho F 2)) a k -> 0 < k -> a + k <= sh Ab \/ sh Ab + nsh (to_Z n) <= a).
    { intros a k Hr Hk. eapply (new_shadow_apart H HHx); [exact Hheap' | exact Hr | rewrite Espu; clear - SB1 Hhl Hlsp Hoff Hoff2 Hcs HB64; slia0 | exact Hk]. }
    (* [comment removed for export] *)
    destruct Xnamed as [XG0in XLB0nd].
    assert (Hclient : forall a, 0 <= a < 2 ^ 64 -> client0 H Q a -> ~ named_addr Q a -> aclient_range H LB (bv_unsigned (rv rho F 2)) a 1).
    { intros a Ha Hcl Hna. rewrite Espu.
      unfold client0, aclient_addr in Hcl. destruct Hcl as [Hs | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
      - left. slia0.
      - right. left. intros a' Ha'. replace a' with a by slia0. exact Hst.
      - destruct (in_dec bptr_eq_dec (blk_id b) (map g_id (q_G0 Q))) as [Hi|Hni].
        + exfalso. apply Hna. apply in_map_iff in Hi as (g0 & Eg & Hg0).
          pose proof (proj1 (Forall_forall _ _) XG0in g0 Hg0) as Hg0in.
          pose proof (nodup_ids_eq _ b _ XLB0nd Hb Hg0in ltac:(rewrite <- Eg; reflexivity)) as ->.
          exists g0. split; [exact Hg0|]. left. cbn [blk_addr blk_size fst snd] in Hr. exact Hr.
        + right. right. left. exists b. split; [exact (XLB0 b Hb Hni)|]. slia0.
      - destruct (in_dec bptr_eq_dec (blk_id b) (map g_id (q_G0 Q))) as [Hi|Hni].
        + exfalso. apply Hna. apply in_map_iff in Hi as (g0 & Eg & Hg0).
          pose proof (proj1 (Forall_forall _ _) XG0in g0 Hg0) as Hg0in.
          pose proof (nodup_ids_eq _ b _ XLB0nd Hb Hg0in ltac:(rewrite <- Eg; reflexivity)) as ->.
          exists g0. split; [exact Hg0|]. right. cbn [blk_addr blk_size fst snd] in Hr. exact Hr.
        + right. right. right. left. exists b. split; [exact (XLB0 b Hb Hni)|]. slia0.
      - do 4 right. left. slia0.
      - do 5 right. left. slia0.
      - do 6 right. slia0. }
    assert (Hclient_addr : forall a, 0 <= a < 2 ^ 64 -> client0 H Q a -> ~ named_addr Q a -> aclient_addr H LB (bv_unsigned (rv rho F 2)) a).
    { intros a Ha Hcl Hna. eapply aclient_range_addr; [exact (Hclient a Ha Hcl Hna) | slia0]. }
    (* [comment removed for export] *)
    pose proof (ah_nodup H HH _ _ _ Hheap') as Hnd'. cbn [map blk_id fst] in Hnd'.
    pose proof (proj1 (NoDup_cons_iff _ _) Hnd') as [Hpfresh HndLB].
    assert (HGids : forall g, In g G -> In (g_id g) (map blk_id LB)).
    { intros g Hg. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _).
      replace (g_id g) with (blk_id (g_id g, g_addr g, to_Z (g_size g))) by reflexivity. apply in_map. exact Hin. }
    (* [comment removed for export] *)
    assert (HPcl : aclient_range H LB (bv_unsigned (rv rho F 2)) P 8).
    { destruct (Uint63.eqb tm 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. destruct (STKm E1) as (_ & SPd & _). left. clear - SPd; subst P; slia0.
      - apply Uint63.eqb_false_spec in E1. destruct (OBJFm E1) as (_ & _ & _ & [(g0 & Hg0 & _ & EgD & EgS)|(f0 & Hf0 & _ & EfD & EfS)]).
        + do 2 right. left. pose proof (proj1 (Forall_forall _ _) XGin g0 Hg0) as (Hin0 & _). exists (g_id g0, g_addr g0, to_Z (g_size g0)).
          split; [exact Hin0| cbn [blk_addr blk_size fst snd]; rewrite EgD, EgS; clear - RNGm Hom0; subst P; slia0].
        + do 4 right. left. destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf0) as [(K1 & K2 & K3 & K4 & K5) _].
          pose proof (proj1 (Forall_forall _ _) XFFin f0 Hf0) as (_ & _ & _ & Hkf0 & _). rewrite EfD in K2, K3. rewrite <- (fsz_eq _ Hkf0) in K3.
          pose proof (f_equal to_Z EfS) as EfS'. rewrite EfS' in K3.
          clear - K2 K3 RNGm Hom0; subst P; unfold AFS_HDR in *; slia0. }
    assert (HfreshP : P + 8 <= Ab \/ Ab + to_Z n <= P) by (exact (Hfresh P 8 HPcl ltac:(clear; slia0))).
    assert (HfreshPS : P + 8 <= sh Ab \/ sh Ab + nsh (to_Z n) <= P) by (exact (HfreshS P 8 HPcl ltac:(clear; slia0))).
    assert (HPclA : forall a, P <= a < P + 8 -> aclient_addr H LB (bv_unsigned (rv rho F 2)) a).
    { intros a Ha. eapply aclient_range_addr; [exact HPcl| exact Ha]. }
    (* [comment removed for export] *)
    set (m1 := write_to_mem (ms_mem ms) (wa P) (le8 (Z_to_bv 64 Ab))) in Hpres.
    assert (HP64 : 0 <= P /\ P + 8 < 2 ^ 64) by (clear - HDm0 Hom0 RNGm HDmhi; subst P; unfold AAPP_HI in HDmhi; slia0).
    assert (M1o : forall w : word, ~ (P <= bv_unsigned w < P + 8) -> m1 w = ms_mem ms w).
    { intros w Hw. subst m1. rewrite write_to_mem_spec by (unfold le8, word_to_le_bytes; rewrite ?length_Z_to_le_bytes; clear - HP64; slia0).
      unfold le8, word_to_le_bytes. rewrite length_Z_to_le_bytes. change (Z.of_nat 8) with 8.
      destruct (Z.leb_spec0 P (bv_unsigned w)); destruct (Z.ltb_spec0 (bv_unsigned w) (P + 8)); cbn [andb]; try reflexivity. exfalso. clear - Hw l0 l1. slia0. }
    assert (MU1 : munch [(P, P + 8)] (ms_mem ms) m1) by (intros w Hw; apply M1o; cbn [outside] in Hw; clear - Hw; slia0).
    assert (WM1 : wmono asegs (ms_mem ms) m1) by (intros w Hw; subst m1; apply wview_write; exact Hw).
    set (mH := fun w : word => if ((P <=? bv_unsigned w) && (bv_unsigned w <? P + 8))%Z then ms_mem ms w else m' w).
    assert (MHi : forall a, P <= a < P + 8 -> mH (wa a) = ms_mem ms (wa a)).
    { intros a Ha. subst mH. cbv beta. rewrite wa_unsigned by (clear - Ha HP64; slia0).
      destruct (Z.leb_spec0 P a) as [L1|L1]; [| exfalso; clear - Ha L1; slia0]. destruct (Z.ltb_spec0 a (P + 8)) as [L2|L2]; [reflexivity| exfalso; clear - Ha L2; slia0]. }
    assert (MHw : forall w : word, ~ (P <= bv_unsigned w < P + 8) -> mH w = m' w).
    { intros w Hw. subst mH. cbv beta. destruct (Z.leb_spec0 P (bv_unsigned w)) as [L1|L1]; [| reflexivity]. destruct (Z.ltb_spec0 (bv_unsigned w) (P + 8)) as [L2|L2]; [exfalso; clear - Hw L1 L2; slia0| reflexivity]. }
    assert (MHo : forall a, 0 <= a < 2 ^ 64 -> ~ (P <= a < P + 8) -> mH (wa a) = m' (wa a)).
    { intros a Ha Hna. apply MHw. rewrite wa_unsigned by (clear - Ha; slia0). exact Hna. }
    assert (MUH : munch [(P, P + 8)] m' mH) by (intros w Hw; apply MHw; cbn [outside] in Hw; clear - Hw; slia0).
    assert (WMH : wmono asegs m' mH).
    { intros w Hw. destruct (Z.leb_spec0 P (bv_unsigned w)) as [L1|L1]; [destruct (Z.ltb_spec0 (bv_unsigned w) (P + 8)) as [L2|L2]|].
      - rewrite <- (wa_id w). unfold wview. rewrite MHi by (clear - L1 L2; slia0). fold (wview asegs (ms_mem ms) (wa (bv_unsigned w))).
        destruct (SRDm (P + 8) ltac:(clear - RNGm; subst P; slia0)) as (_ & _ & SS). exact (proj1 (SS (bv_unsigned w) ltac:(clear - L1 L2; slia0))).
      - unfold wview in Hw |- *. rewrite MHw by (clear - L2; slia0). exact Hw.
      - unfold wview in Hw |- *. rewrite MHw by (clear - L1; slia0). exact Hw. }
    (* [comment removed for export] *)
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> aclient_addr H LB (bv_unsigned (rv rho F 2)) a ->
                     rview asegs mH (wa a) = rview asegs (ms_mem ms) (wa a)
                     /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs mH (wa a) <> None)).
    { intros a Ha Hc. destruct (Z.lt_ge_cases a P) as [L|L]; [| destruct (Z.lt_ge_cases a (P + 8)) as [L'|L']].
      2: { apply pw_keep. apply MHi. clear - L L'. slia0. }
      all: destruct (Hpres a Ha Hc) as [E W]; rewrite (M1o (wa a)) in E by (rewrite wa_unsigned by (clear - Ha; slia0); first [clear - L L'| clear - L]; slia0);
           split; [apply rview_eq_of_mem; rewrite MHo by (first [exact Ha| clear - L L'; slia0| clear - L; slia0]); exact E
                 | intros Wv; unfold wview; rewrite MHo by (first [exact Ha| clear - L L'; slia0| clear - L; slia0]); fold (wview asegs m' (wa a)); apply W; apply WM1; exact Wv]. }
    assert (HpresH : apres H LB (bv_unsigned (rv rho F 2)) (ms_mem ms) mH).
    { intros a Ha Hc. destruct (Z.lt_ge_cases a P) as [L|L]; [| destruct (Z.lt_ge_cases a (P + 8)) as [L'|L']].
      2: { apply pw_keep'. apply MHi. clear - L L'. slia0. }
      all: destruct (Hpres a Ha Hc) as [E W]; rewrite (M1o (wa a)) in E by (rewrite wa_unsigned by (clear - Ha; slia0); first [clear - L L'| clear - L]; slia0);
           split; [rewrite MHo by (first [exact Ha| clear - L L'; slia0| clear - L; slia0]); exact E
                 | intros Wv; unfold wview; rewrite MHo by (first [exact Ha| clear - L L'; slia0| clear - L; slia0]); fold (wview asegs m' (wa a)); apply W; apply WM1; exact Wv]. }
    assert (HacH : ACONST mH) by (eapply ACONST_frame; [exact Hac'| exact MUH| exact WMH| apply Forall_cons; [exact ACOm| apply Forall_nil]]).
    assert (HinvH : mem_inv asegs mH).
    { intros w b Hw. destruct (Z.leb_spec0 P (bv_unsigned w)) as [L1|L1]; [destruct (Z.ltb_spec0 (bv_unsigned w) (P + 8)) as [L2|L2]|].
      - rewrite <- (wa_id w) in Hw |- *. rewrite MHi in Hw by (clear - L1 L2; slia0). exact (Xinv _ _ Hw).
      - rewrite MHw in Hw by (clear - L2; slia0). exact (Hinv' _ _ Hw).
      - rewrite MHw in Hw by (clear - L1; slia0). exact (Hinv' _ _ Hw). }
    assert (HerrH : rw_cells asegs mH (bv_unsigned (rv rho F 4) + -164) [C4 errv']).
    { eapply rw_cells_transport; [exact Herr'| exact MUH| exact WMH|]. cbn [cells_size csize disjoint_from]. split; [| exact I].
      rewrite EerrA. left. clear - Eerr H0 H1 HDmtop Hom0; subst P. unfold errA, AERRNO, ATP, AIMG_TOP in *. slia0. }
    assert (HadH : addressable mH Ab (to_Z n)).
    { eapply addressable_transport; [exact Had| exact MUH| exact WMH|]. cbn [disjoint_from]. split; [clear - HfreshPS; slia0| exact I]. }
    assert (HblkH : rw_cells asegs mH Ab [Cells.CB (Z.to_nat (to_Z n)) junk]).
    { eapply rw_cells_transport; [exact Hblk| exact MUH| exact WMH|]. cbn [cells_size csize disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn1; slia0). split; [clear - HfreshP; slia0| exact I]. }
    assert (HstkH : stk asegs mH (q_lo Q) (bv_unsigned (rv rho F 2))).
    { apply (stk_pres asegs m'); [exact Hstk'|]. intros a Ha. apply pw_keep'. apply MHo; [clear - Ha SB1 HspB Hoff2 Espu HB64 ACEILB; slia0| clear - Ha LODm; unbox LODm; slia0]. }
    (* [comment removed for export] *)
    destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [Hdu1 Hkd1].
    assert (INB1 : rg_inb (drop_below off rg1)).
    { intros pn p' ci cc Hp' Hc'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->). unfold drop_below. cbn [rg_len].
      unfold drop_page in Hc'. cbn [fst snd] in Hc'. destruct (pn =? off >> 12)%uint63.
      - cbn [pg_cells] in Hc'. destruct (keep_cells_ge_inv _ _ _ _ Hc') as [_ Hc'']. exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'').
      - exact (Xinb 1%uint63 rg1 pn p0 ci cc Hrg1 Hp0 Hc'). }
    assert (UNK1 : rg_unk (drop_below off rg1)).
    { split; [exact Hlo1|]. split; [exact Hd1|]. intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
      unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hkd1 _ _ Hp0). }
    assert (GEOm : rg_len rgm1 = rg_len rgm /\ rg_lo rgm1 = 0%uint63 /\ rg_unk rgm1 /\ rg_inb rgm1 /\ rg_align rgm1 = rg_align rgm /\ rg_kind rgm1 = rg_kind rgm /\ rg_dflt rgm1 = Some PKUnk).
    { pose proof Hrgm1 as X1. rewrite iget_iset in X1. destruct (tm =? 1)%uint63 eqn:E1.
      - apply Uint63.eqb_spec in E1. injection X1 as <-. assert (Ergm : rgm = rg1) by (rewrite E1 in Hrgm; clear - Hrgm Hrg1; congruence). rewrite Ergm.
        split; [reflexivity|]. split; [exact Hlo1|]. split; [exact UNK1|]. split; [exact INB1|]. split; [reflexivity|]. split; [reflexivity|]. cbn [drop_below rg_dflt]. exact Hd1.
      - rewrite Hrgm in X1. injection X1 as <-. split; [reflexivity|]. split; [exact Hlodm|]. split; [split; [exact Hlodm| split; [exact Hdfdm| exact Hkddm]]|].
        split; [exact (fun pn p ci cc Hp Hc => Xinb tm rgm pn p ci cc Hrgm Hp Hc)|]. repeat split; try reflexivity. exact Hdfdm. }
    destruct GEOm as (Gmlen & Gmlo & Gmunk & Gminb & Gmal & Gmkd & Gmdf).
    assert (PARTm : mem_part asegs IM rho (ms_mem ms) tm rgm1).
    { pose proof Hrgm1 as X1. rewrite iget_iset in X1. destruct (tm =? 1)%uint63 eqn:E1; [| rewrite Hrgm in X1; injection X1 as <-; exact (mem_part_of _ _ _ _ _ _ _ Hmem Hrgm)].
      apply Uint63.eqb_spec in E1. injection X1 as <-. rewrite E1.
      apply (stack_part asegs IM rho (ms_mem ms) (ms_mem ms) rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q)).
      - exact Xr1.
      - exact Hlo1.
      - exact Hd1.
      - exact Hkd1.
      - rewrite Hlen1; reflexivity.
      - rewrite Hlen1; clear - Hoff Hoff2; slia0.
      - clear - Hoff16 Hoff; smod Hoff16; Z.div_mod_to_equations; slia0.
      - exact (mem_part_of _ _ _ _ _ _ _ Hmem Hrg1).
      - exact Xstk.
      - clear - Hhl Hlsp ACEILB; slia0.
      - rewrite <- Espu; exact Hstk_lo.
      - intros a Ha; split; [reflexivity| intros Wv; exact Wv]. }
    destruct (write_cell_sound asegs IM rho _ tm offm (FV t w_zero) _ rgm1 (ms_mem ms) HWC Hrgm1 PARTm Htm0 Gmunk Gminb ltac:(rewrite Gmlen; exact Hom) Hal8)
      as (_ & _ & UNKW & INBW & (W1lo & W1len & W1al & W1kd & W1df) & _).
    (* [comment removed for export] *)
    assert (TMG : forall g, In g G -> (g_tag g + 1)%uint63 <> tm).
    { intros g Hg E. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & Htg1 & Htg2 & _). pose proof (i63_range (g_tag g)) as Htg.
      assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      destruct (Uint63.eqb tm 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. rewrite E1 in E. apply (f_equal to_Z) in E. rewrite Etg1 in E. change (to_Z 1%uint63) with 1 in E. clear - E Htg1. slia0.
      - apply Uint63.eqb_false_spec in E1. destruct (OBJFm E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
        + destruct XTsep as (S1 & _). destruct (S1 g g0 Hg Hg0) as [DD|DD].
          * intros Egg. subst g0. rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd. slia0.
          * rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd DD. slia0.
          * rewrite <- E in Etd. apply (f_equal to_Z) in Etd. rewrite Etg1 in Etd. clear - Etd DD. slia0.
        + destruct XTsep as (_ & S2 & _). destruct (S2 g f0 Hg Hf0) as [DD|DD]; rewrite <- E in Etd; apply (f_equal to_Z) in Etd; rewrite Etg1 in Etd; clear - Etd DD; slia0. }
    assert (TMF : forall f, In f FF -> (f_tag f + 1)%uint63 <> tm /\ (f_tag f + 2)%uint63 <> tm).
    { intros f Hf. pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & Htg1 & Htg2 & _). pose proof (i63_range (f_tag f)) as Htg.
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; clear - Htg2 Htg Hn59; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; clear - Htg2 Htg Hn59; slia0).
      assert (GEN : forall x, to_Z x = to_Z (f_tag f) + 1 \/ to_Z x = to_Z (f_tag f) + 2 -> x <> tm).
      { intros x Hx E. subst x. destruct (Uint63.eqb tm 1) eqn:E1.
        - apply Uint63.eqb_spec in E1. rewrite E1 in Hx. change (to_Z 1%uint63) with 1 in Hx. clear - Hx Htg1. slia0.
        - apply Uint63.eqb_false_spec in E1. destruct (OBJFm E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
          + destruct XTsep as (_ & S2 & _). destruct (S2 g0 f Hg0 Hf) as [DD|DD]; rewrite Etd in DD; clear - Hx DD; slia0.
          + destruct XTsep as (_ & _ & S3). destruct (S3 f f0 Hf Hf0) as [DD|DD].
            * intros Eff. subst f0. rewrite Etd in Hx. clear - Hx. slia0.
            * rewrite Etd in DD. clear - Hx DD. slia0.
            * rewrite Etd in DD. clear - Hx DD. slia0. }
      split; apply GEN; [left; exact Etg1| right; exact Etg2]. }
    assert (TM23 : tm <> 2%uint63 /\ tm <> 3%uint63).
    { destruct (Uint63.eqb tm 1) eqn:E1; [apply Uint63.eqb_spec in E1; rewrite E1; split; intros E; discriminate E|].
      apply Uint63.eqb_false_spec in E1. destruct (OBJFm E1) as (_ & _ & _ & [(g0 & Hg0 & Etd & _)|(f0 & Hf0 & Etd & _)]).
      - pose proof (proj1 (Forall_forall _ _) XGin g0 Hg0) as (_ & _ & _ & Htg1 & _). rewrite Etd in Htg1.
        split; intros E; rewrite E in Htg1; [change (to_Z 2%uint63) with 2 in Htg1| change (to_Z 3%uint63) with 3 in Htg1]; clear - Htg1; slia0.
      - pose proof (proj1 (Forall_forall _ _) XFFin f0 Hf0) as (_ & _ & _ & _ & Htg1 & _). rewrite Etd in Htg1.
        split; intros E; rewrite E in Htg1; [change (to_Z 2%uint63) with 2 in Htg1| change (to_Z 3%uint63) with 3 in Htg1]; clear - Htg1; slia0. }
    destruct TM23 as [TM2 TM3].
    assert (Htmt : (tm =? t)%uint63 = false) by (destruct (tm =? t)%uint63 eqn:E; [apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; exfalso; clear - E Htm_lt; slia0| reflexivity]).
    pose proof (proj2 (Uint63.eqb_false_spec _ _) Htm0) as Htm0f.
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 0)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    exists s', ((p, Ab, to_Z n) :: LB), (GB t p Ab n :: G), FF, XS, ms1.
    assert (HRn' : Rn asegs IM (t + 17)%uint63 rho'
              (FS (ret_of l) (iset 10 (FV 0 w_zero) (clobber clob14 (t + 2) (f_regs F)))
                  (iset 0 (err_region K (t + 16) rg0 pe) (iset (t + 1) (sh_region false t n) (iset t (blk_region n lg iempty) (iset tm rgW (iset 1 (drop_below off rg1) (f_mem F)))))) None)
              ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree t rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Et17; slia0]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z t + 17 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Et17; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''t : rho'' t = wa Ab) by (rewrite Erho'' by slia0; exact Erho't).
      assert (Erho''s : rho'' (t + 1)%uint63 = wa (sh Ab)) by (rewrite Erho'' by (rewrite Et1; slia0); exact Erho's).
      assert (Erho''old : forall x, to_Z x < to_Z t -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by slia0. subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; slia0); exact Xr1).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 0)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; Z_to_bv 64 0;
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
        assert (Hcl : forall k : int, iget k (clobber clob14 (t + 2) (f_regs F)) =
                      match index_of k clob14 with
                      | Some i => Some (FV (of_Z (to_Z (t + 2)%uint63 + Z.of_nat i)) w_zero)
                      | None => iget k (f_regs F) end).
        { intros k. apply iget_clobber; [exact Hnd14 | rewrite Et2; cbn [length clob14]; slia0]. }
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
            match goal with |- Z_to_bv 64 0 = dv ?rr (FV 0%uint63 w_zero) => unfold w_zero; rewrite (dv_conc63 rr 0%uint63 Hrho''0); reflexivity end
          | (* [comment removed for export] *)
            match goal with |- _ = dv ?rr (FV (of_Z (to_Z ?t1 + Z.of_nat ?i)) w_zero) =>
              let Etag := fresh "Etag" in
              assert (Etag : to_Z (of_Z (to_Z t1 + Z.of_nat i)) = to_Z t1 + Z.of_nat i)
                by (rewrite Uint63.of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); slia0);
              rewrite (dv_tag_zero rr (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia0);
              rewrite (Erho'' (of_Z (to_Z t1 + Z.of_nat i))) by (rewrite Etag; slia0);
              rewrite (EL17 (of_Z (to_Z t1 + Z.of_nat i)) (S (S i))); [reflexivity | slia0 | rewrite Etag; slia0]
            end
          | (* [comment removed for export] *)
            match goal with |- rv _ _ ?kz = dv _ match iget ?ki (f_regs ?FF) with _ => _ end =>
              rewrite <- (rget_regs' FF ki eq_refl);
              let kn := eval vm_compute in (Z.to_nat kz) in
              let HP := fresh "HP" in
              pose proof (Hpre kn ltac:(slia0)) as HP; cbn [nth Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in HP; exact HP
            end
          ].
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        cbn [f_mem ms_mem].
        assert (Hrg0M : iget 0%uint63 (f_mem F) = Some rg0).
        { revert Hrg0'. rewrite !iget_iset.
          destruct (0 =? t + 1)%uint63 eqn:E01; [apply Uint63.eqb_spec in E01; apply (f_equal to_Z) in E01; rewrite Et1 in E01; change (to_Z 0%uint63) with 0 in E01; clear - E01 Xn0a Xn0b; slia0|].
          destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; apply (f_equal to_Z) in Et0; change (to_Z 0%uint63) with 0 in Et0; clear - Et0 Xn0a Xn0b; slia0|].
          destruct (0 =? tm)%uint63 eqn:E0m; [apply Uint63.eqb_spec in E0m; exfalso; exact (Htm0 (eq_sym E0m))|].
          change ((0 =? 1)%uint63) with false. cbv iota. intros E; exact E. }
        rewrite Hrg0M in Hrg0_. injection Hrg0_ as Erg0. subst rg0_.
        (* [comment removed for export] *)
        assert (Hnewsep : forall t' rg', iget t' (f_mem F) = Some rg' ->
                  (Ab + to_Z n <= bv_unsigned (rho'' t') + to_Z (rg_lo rg') \/ bv_unsigned (rho'' t') + to_Z (rg_len rg') <= Ab)
                  /\ (sh Ab + nsh (to_Z n) <= bv_unsigned (rho'' t') + to_Z (rg_lo rg') \/ bv_unsigned (rho'' t') + to_Z (rg_len rg') <= sh Ab)).
        { intros t' rg' Ht'. pose proof (sh_aapp_range Ab (to_Z n) R7 R3) as (Q1 & Q2 & Q3).
          destruct (Xdom t' rg' Ht') as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl]]]]]]]].
          - rewrite Hrg0M in Ht'. injection Ht' as <-. rewrite Hrho''0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0.
            pose proof (sh_above_image Ab ltac:(slia0)) as SAI. clear - SAI R4. unfold AIMG_TOP, AIMG_LO in *. slia0.
          - rewrite Hrg1 in Ht'. injection Ht' as <-. rewrite Erho''1, Hlo1, Hlen1. change (to_Z 0%uint63) with 0.
            rewrite wa_unsigned by (clear - Hhl Hlsp HspB HB64 Hcs ACEILB; slia0). clear - Q2 Q3 R5 Hhl Hlsp ACEILB. unfold AHI_LO in Q3. slia0.
          - rewrite Xreg2 in Ht'. injection Ht' as <-. rewrite (Erho''old 2%uint63) by (change (to_Z 2%uint63) with 2; slia0). rewrite Xr2.
            unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (c_stack K)) by slia0. change (to_Z 0%uint63) with 0. fold (nsh (to_Z (c_stack K))).
            
            assert (SR : sh aceil <= sh (q_sp0 Q - to_Z (c_stack K)) /\ sh (q_sp0 Q - to_Z (c_stack K)) + nsh (to_Z (c_stack K)) <= sh (q_sp0 Q)
                         /\ sh (q_sp0 Q) <= AHI_LO /\ AIMG_TOP <= sh (q_sp0 Q - to_Z (c_stack K))).
            { split; [apply sh_mono; slia0|]. split; [| split].
              - clear - Hsp32 Hcs Est16. smod Hsp32. smod Est16. unfold nsh, sh. Z.div_mod_to_equations. slia0.
              - clear - SB2 Hshi. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia0.
              - apply sh_above_image. slia0. }
            rewrite wa_unsigned by (clear - SR Hcs; unfold AIMG_TOP, AHI_LO, nsh in SR; Z.div_mod_to_equations; slia0).
            destruct R7 as [[P1 P2]|[P1 P2]].
            + assert (TMP2 : 0 <= aceil < AAPP_HI) by (unfold AAPP_HI; slia0). pose proof (sh_in_shadowland aceil TMP2) as SL.
              clear - SR Q1 Q2 Q3 P1 P2 SL R3. unfold ALOWSH_LO, AHI_LO in *. slia0.
            + clear - SR Q1 Q2 Q3 P1 P2 R3. unfold AHI_LO in *. slia0.
          - rewrite Xreg3 in Ht'. injection Ht' as <-. rewrite (Erho''old 3%uint63) by (change (to_Z 3%uint63) with 3; slia0). rewrite Xr3, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
            unfold abs_region. cbn [rg_lo rg_len].
            destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
            apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. rewrite Hslo, Hslen.
            destruct R7 as [[P1 P2]|[P1 P2]]; clear - P1 P2 R1 R3 Hslo Hslen ACEILB ACEILM; smod ACEILM; unfold sh, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *; rewrite ASHADOW_BASE_val in *; Z.div_mod_to_equations; slia0.
          - apply in_map_iff in Hb as (g & <- & Hg).
            pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
            rewrite Hgg in Ht'. injection Ht' as <-. rewrite Hlog, Hleng. change (to_Z 0%uint63) with 0.
            rewrite (Erho''old (g_tag g)) by slia0. rewrite Hrg. pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
            rewrite wa_unsigned by (clear - G1 G3 G5 ACEILB; slia0).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (g_addr g) (to_Z (g_size g))).
            { right; right; left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr blk_size fst snd]; slia0]. }
            destruct (Hfresh _ _ CR ltac:(slia0)) as [D1|D1]; destruct (HfreshS _ _ CR ltac:(slia0)) as [D2|D2]; clear - D1 D2; slia0.
          - apply in_map_iff in Hbs as (g & <- & Hg).
            pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hsh). destruct (Hsh rg' Ht') as (-> & Hrs & _).
            pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _ & G7).
            unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 ACEILB; slia0). change (to_Z 0%uint63) with 0. fold (nsh (to_Z (g_size g))).
            pose proof (i63_range (g_tag g)).
            rewrite (Erho''old (g_tag g + 1)%uint63) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia0). rewrite Hrs.
            pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 G3) as (U1 & U2 & U3). pose proof (sh_above_image (g_addr g) ltac:(slia0)) as SAI.
            rewrite wa_unsigned by (clear - U2 U3 SAI G1 Hsz; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia0).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (sh (g_addr g)) (nsh (to_Z (g_size g)))).
            { right; right; right; left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr blk_size fst snd]; slia0]. }
            assert (Kn : 0 < nsh (to_Z (g_size g))) by (clear - Hsz; unfold nsh; Z.div_mod_to_equations; slia0).
            destruct (Hfresh _ _ CR Kn) as [D1|D1]; destruct (HfreshS _ _ CR Kn) as [D2|D2]; clear - D1 D2; slia0.
          - apply in_map_iff in Hf as (f & <- & Hf).
            pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
            rewrite Hgf in Ht'. injection Ht' as <-. rewrite Hlof, Hlenf, (fsz_eq _ Hk). change (to_Z 0%uint63) with 0.
            rewrite (Erho''old (f_tag f)) by slia0. rewrite Hf0.
            destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia0)) as FP.
            rewrite wa_unsigned by (clear - K2 K3 F1 F2 FP ACEILB; unfold AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia0).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (f_ff f) (AsIface.fsz (to_Z (f_k f)))).
            { do 4 right. left. unfold AFS_HDR in *. slia0. }
            destruct (Hfresh _ _ CR ltac:(slia0)) as [D1|D1]; destruct (HfreshS _ _ CR ltac:(slia0)) as [D2|D2]; clear - D1 D2; slia0.
          - apply in_map_iff in Hfs as (f & <- & Hf).
            pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
            rewrite Hgs in Ht'. injection Ht' as <-. rewrite Hlos, Hlens. change (to_Z 0%uint63) with 0.
            pose proof (i63_range (f_tag f)).
            rewrite (Erho''old (f_tag f + 1)%uint63) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia0). rewrite Hf1.
            destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia0)) as FP.
            pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia0)) as [E1 E2].
            assert (B : AIMG_TOP <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) <= AAPP_HI) by (clear - K2 K3 F1 F2 ACEILB FP; unfold AIMG_TOP, AFS_HDR, AFS_SIZE, AAPP_HI in *; slia0).
            pose proof (sh_above_image (f_ff f) ltac:(unfold AIMG_TOP in B; slia0)) as SA1. pose proof (sh_nsh_high (f_ff f) (AsIface.fsz (to_Z (f_k f))) ltac:(unfold AIMG_TOP in B; slia0) ltac:(slia0) (proj2 B)) as SA2.
            rewrite wa_unsigned by (clear - B SA1 SA2 FP; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia0).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (sh (f_ff f)) (fshn (to_Z (f_k f)))).
            { do 5 right. left. pose proof (sh_mono (as_FSB H) (f_ff f) ltac:(unfold AFS_HDR in *; slia0)).
              assert (sh (f_ff f) + fshn (to_Z (f_k f)) <= sh (as_FSB H + AFS_SIZE)).
              { rewrite E1. pose proof (frame_al8 H _ _ _ (conj K1 (conj K2 (conj K3 (conj K4 K5))))) as A8. clear - K3 A8 E2 FP. unfold nsh, sh. Z.div_mod_to_equations. slia0. }
              slia0. }
            assert (Kn : 0 < fshn (to_Z (f_k f))) by (rewrite E1; clear - FP; unfold nsh; Z.div_mod_to_equations; slia0).
            destruct (Hfresh _ _ CR Kn) as [D1|D1]; destruct (HfreshS _ _ CR Kn) as [D2|D2]; clear - D1 D2; slia0.
          - apply in_map_iff in Hfl as (f & <- & Hf).
            pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & _ & Hflg & _).
            rewrite Hflg in Ht'. injection Ht' as <-. unfold flag_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
            pose proof (i63_range (f_tag f)).
            rewrite (Erho''old (f_tag f + 2)%uint63) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia0). rewrite Hf2.
            destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _].
            rewrite wa_unsigned by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia0).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (f_fp f) 1).
            { do 4 right. left. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. slia0. }
            destruct (Hfresh _ _ CR ltac:(slia0)) as [D1|D1]; destruct (HfreshS _ _ CR ltac:(slia0)) as [D2|D2]; clear - D1 D2; slia0. }
        set (TM := iset 0 (err_region K (t + 16) rg0 pe) (iset (t + 1) (sh_region false t n) (iset t (blk_region n lg iempty) (iset 1 (drop_below off rg1) (f_mem F))))).
        (* [comment removed for export] *)
        assert (PARTSH : forall t' rg', iget t' TM = Some rg' -> mem_part asegs IM rho'' mH t' rg').
        { intros t' rg' Ht'. subst TM. rewrite !iget_iset in Ht'.
          destruct (t' =? 0)%uint63 eqn:E0.
          * (* [comment removed for export] *) apply Uint63.eqb_spec in E0. subst t'. injection Ht' as <-.
            eapply (region0_part asegs IM rho'' Hrho''0 IMX eq_refl HIMX HWRX K (ms_mem ms) mH rg0 pe (t + 16)%uint63 errv'
                      (fun c => 0 <= c /\ c + 8 <= AIMG_TOP /\ ((exists x, In x (c_xw K) /\ to_Z x = c)
                                                           \/ (exists cc, In (of_Z c, cc) (c_ro K) /\ aconst_pin_b (of_Z c) cc = false)))).
            -- exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg0M).
            -- exact Hd0.
            -- exact Hpg0.
            -- intros pn p0 ci c Hp0 Hc. pose proof (i63_range pn) as Rpn. pose proof (i63_range ci) as Rci.
               destruct (Xinb 0%uint63 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hcb [Hci512 _]]. rewrite Hlen0 in Hcb.
               destruct (Hc0 rg0 pn p0 ci c Hrg0M Hp0 Hc) as [Hx | [He | (cc & Hcc)]].
               ** left. split; [slia0|]. split; [clear -Hcb; unfold AIMG_TOP in *; slia0|]. left; exact Hx.
               ** right; left; exact He.
               ** destruct (aconst_pin_b (of_Z (to_Z pn * 4096 + to_Z ci * 8)) cc) eqn:Epin.
                  --- (* [comment removed for export] *)
                      right; right. destruct (aconst_pin_sound mH _ cc HacH Epin) as (sl & -> & Hsl).
                      assert (Ea : to_Z (of_Z (to_Z pn * 4096 + to_Z ci * 8)) = to_Z pn * 4096 + to_Z ci * 8)
                        by (apply toZ_of_Z_small; clear -Hcb Rpn Rci; unfold AIMG_TOP in *; slia0).
                      pose proof (ro_okb_sound K (f_mem F) rg0 _ (CB sl) pn p0 ci c Hrook Hrg0M Hcc Hp0 Hc (eq_sym Ea) ltac:(clear -Hci512 Rci; slia0)) as ->.
                      exists sl. split; [reflexivity|]. intros j Hj. pose proof (Hsl rho'' j Hj) as T. rewrite Ea in T. exact T.
                  --- left. split; [slia0|]. split; [clear -Hcb; unfold AIMG_TOP in *; slia0|]. right. exists cc. split; [exact Hcc | exact Epin].
            -- intros c a (Hcc0 & Hc8 & [(x & Hx & <-) | (cc & Hcc & Hnp)]) Ha.
               ++ clear - Hkeep Hx Ha Hcc0 Hc8 HK Espu Hoff Hcs Hlsp Hhl ACEILB. hk_xw x Hx.
                  apply (proj1 (Hkeep a ltac:(unfold AIMG_TOP in *; slia0) ltac:(right; left; eapply aimg8_b_spec; [|exact Ha]; unfold aimg8_b; unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in *;
                           rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le; slia0))).
               ++ destruct (aimg8_b c) eqn:E8.
                  ** apply (proj1 (Hkeep a ltac:(unfold AIMG_TOP in *; slia0) ltac:(right; left; exact (aimg8_b_spec _ _ E8 Ha)))).
                  ** pose proof (HROC _ _ Xac HacH Xinv HinvH (of_Z c) cc Hcc) as E. rewrite toZ_of_Z_small in E by (unfold AIMG_TOP in *; slia0).
                     specialize (E E8 Hnp (a - c) ltac:(slia0)). replace (c + (a - c)) with a in E by slia0. exact E.
            -- exact Hpe.
            -- exact HinvH.
            -- rewrite EerrA in HerrH. exact HerrH.
            -- rewrite dv_tag_zero by (rewrite Et16; slia0). rewrite Erho'' by (rewrite Et16; slia0). exact Erho'e.
            -- exact Eerr8.
            -- exact Ebi.
            -- destruct (err_page_ok_inv _ _ Hep) as (rg0b & pb & Hrg0b & Hir & _). fold F in Hrg0b. rewrite Hrg0M in Hrg0b. injection Hrg0b as <-.
               unfold in_region in Hir. rewrite !andb_true_iff in Hir. destruct Hir as [[[Hob _] _] Hir]. apply Uint63.leb_spec in Hir.
               apply Uint63.ltb_spec in Hob. change (to_Z off_bound) with (2 ^ 62) in Hob.
               rewrite Uint63.add_spec in Hir. change (to_Z 8%uint63) with 8 in Hir. change wB with (2 ^ 63) in Hir.
               pose proof (i63_range (rg_len rg0)). rewrite Z.mod_small in Hir by slia0. exact Hir.
            -- rewrite Hlen0. reflexivity.
          * destruct (t' =? t + 1)%uint63 eqn:Ets.
            -- (* [comment removed for export] *) apply Uint63.eqb_spec in Ets. subst t'. injection Ht' as <-.
               apply (sh_region_part IM rho'' Hrho''0 false mH t n Ab).
               ++ exact Erho''s.
               ++ rewrite Erho''t. apply wa_unsigned. slia0.
               ++ slia0.
               ++ slia0.
               ++ clear - R5 ACEILB. unfold AAPP_HI. slia0.
               ++ exact (proj2 HadH).
            -- destruct (t' =? t)%uint63 eqn:Et'.
               ++ (* [comment removed for export] *) apply Uint63.eqb_spec in Et'. subst t'. injection Ht' as <-.
                  apply (blk_region_part asegs IM rho'' mH t n lg Ab Erho''t).
                  ** intros E. pose proof (f_equal to_Z E). change (to_Z 0%uint63) with 0 in *. slia0.
                  ** slia0.
                  ** split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [clear - R5 ACEILB; slia0 | exact I].
                  ** unbox Elg. smod HAal. rewrite Elg. exact HAal.
                  ** clear - Hlg46; slia0.
                  ** slia0.
                  ** destruct HblkH as [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by slia0. exact Hw.
               ++ destruct (t' =? 1)%uint63 eqn:E1.
                  ** (* [comment removed for export] *) apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
                     apply (stack_part asegs IM rho'' (ms_mem ms) mH rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q)).
                     --- exact Erho''1.
                     --- exact Hlo1.
                     --- exact Hd1.
                     --- exact Hkd1.
                     --- rewrite Hlen1. reflexivity.
                     --- rewrite Hlen1. slia0.
                     --- clear - Hoff16 Hoff. smod Hoff16. Z.div_mod_to_equations. slia0.
                     --- exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1).
                     --- exact Xstk.
                     --- slia0.
                     --- rewrite <- Espu. exact HstkH.
                     --- intros a Ha. destruct Xstk as (_ & H64 & _). apply Hkeep; [slia0 | left; rewrite Espu; slia0].
                  ** (* [comment removed for export] *)
                     assert (Hne0 : t' <> 0%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E0; discriminate).
                     assert (Hne1 : t' <> 1%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E1; discriminate).
                     apply (old_parts H IMX A HK HHx HSH0 _ _ _ _ _ _ _ _ _ _ _ rho'' mH LB (bv_unsigned (rv rho F 2)) [] t' rg' X).
                     --- intros x Hx. apply Erho''old. exact Hx.
                     --- exact Hkeep.
                     --- rewrite Espu. slia0.
                     --- intros g Hg _. exact (proj1 (proj1 (Forall_forall _ _) XGin g Hg)).
                     --- intros b Hb. exact Hb.
                     --- exact HacH.
                     --- exact HinvH.
                     --- exact Ht'.
                     --- exact Hne0.
                     --- exact Hne1.
                     --- intros g _ []. }
        assert (SEPM : forall t1 t2 r1 r2, t1 <> t2 -> iget t1 TM = Some r1 -> iget t2 TM = Some r2 ->
                  bv_unsigned (rho'' t1) + to_Z (rg_len r1) <= bv_unsigned (rho'' t2) + to_Z (rg_lo r2) \/ bv_unsigned (rho'' t2) + to_Z (rg_len r2) <= bv_unsigned (rho'' t1) + to_Z (rg_lo r1)).
        {          intros t1 t2 r1 r2 Hne Hi1 Hi2. subst TM. rewrite !iget_iset in Hi1, Hi2.
          (* [comment removed for export] *)
          assert (Hold : forall t' rg', t' <> t -> t' <> (t + 1)%uint63 ->
                    (if (t' =? 0)%uint63 then Some (err_region K (t + 16) rg0 pe)
                     else if (t' =? t + 1)%uint63 then Some (sh_region false t n)
                     else if (t' =? t)%uint63 then Some (blk_region n lg iempty)
                     else if (t' =? 1)%uint63 then Some (drop_below off rg1) else iget t' (f_mem F)) = Some rg' ->
                    exists rg, iget t' (f_mem F) = Some rg /\ rg_lo rg = rg_lo rg' /\ rg_len rg = rg_len rg').
          { intros t' rg' Hne' Hne'' Ht'.
            destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; subst t'; injection Ht' as <-; exists rg0; split; [exact Hrg0M | split; reflexivity]|].
            destruct (t' =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; congruence|].
            destruct (t' =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; congruence|].
            destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; subst t'; injection Ht' as <-; exists rg1; split; [exact Hrg1 | split; reflexivity]|].
            exists rg'. split; [exact Ht' | split; reflexivity]. }
          assert (Ht0f : (t =? 0)%uint63 = false).
          { destruct (t =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. change (to_Z 0%uint63) with 0 in E. slia0. }
          assert (Hts0f : (t + 1 =? 0)%uint63 = false).
          { destruct (t + 1 =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. change (to_Z 0%uint63) with 0 in E. slia0. }
          assert (Htst : (t =? t + 1)%uint63 = false).
          { destruct (t =? t + 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. slia0. }
          (* [comment removed for export] *)
          assert (Enew : forall t' r', (t' = t \/ t' = (t + 1)%uint63) ->
                    (if (t' =? 0)%uint63 then Some (err_region K (t + 16) rg0 pe)
                     else if (t' =? t + 1)%uint63 then Some (sh_region false t n)
                     else if (t' =? t)%uint63 then Some (blk_region n lg iempty)
                     else if (t' =? 1)%uint63 then Some (drop_below off rg1) else iget t' (f_mem F)) = Some r' ->
                    (t' = t /\ bv_unsigned (rho'' t') + to_Z (rg_lo r') = Ab /\ bv_unsigned (rho'' t') + to_Z (rg_len r') = Ab + to_Z n)
                    \/ (t' = (t + 1)%uint63 /\ bv_unsigned (rho'' t') + to_Z (rg_lo r') = sh Ab /\ bv_unsigned (rho'' t') + to_Z (rg_len r') = sh Ab + nsh (to_Z n))).
          { intros t' r' [-> | ->] Hr'.
            - rewrite Ht0f, Htst, Uint63.eqb_refl in Hr'. cbv iota in Hr'. injection Hr' as <-. left. unfold blk_region. cbn [rg_lo rg_len].
              change (to_Z 0%uint63) with 0. rewrite Erho''t, wa_unsigned by slia0. repeat split; slia0.
            - rewrite Hts0f, Uint63.eqb_refl in Hr'. cbv iota in Hr'. injection Hr' as <-. right. unfold sh_region. cbn [rg_lo rg_len].
              change (to_Z 0%uint63) with 0. rewrite (nsh_eq n) by slia0. rewrite Erho''s.
              pose proof (sh_aapp_range Ab (to_Z n) R7 R3) as (Q1 & Q2 & Q3). pose proof (sh_above_image Ab ltac:(slia0)) as SAI.
              rewrite wa_unsigned by (clear - Q2 Q3 SAI R3 Hn1; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia0).
              repeat split; slia0. }
          (* [comment removed for export] *)
          pose proof (aapp_disjoint_sh Ab (to_Z n) Ab (to_Z n) R7 ltac:(slia0) ltac:(clear - R5 ACEILB; unfold AAPP_HI; slia0) R3) as Hbs.
          assert (NE01 : forall x : int, x = t -> x = (t + 1)%uint63 -> False).
          { intros x -> E. apply (f_equal to_Z) in E. rewrite Et1 in E. slia0. }
          destruct (Z.eq_dec (to_Z t1) (to_Z t)) as [E1t|E1t].
          * apply to_Z_inj in E1t. subst t1.
            destruct (Enew t r1 (or_introl eq_refl) Hi1) as [(_ & A1 & B1)|(E & _)]; [| exfalso; exact (NE01 t eq_refl E)].
            destruct (Z.eq_dec (to_Z t2) (to_Z (t + 1)%uint63)) as [E2s|E2s].
            -- apply to_Z_inj in E2s. subst t2.
               destruct (Enew (t + 1)%uint63 r2 (or_intror eq_refl) Hi2) as [(E & _)|(_ & A2 & B2)]; [exfalso; symmetry in E; exact (NE01 t eq_refl E)|].
               clear - A1 B1 A2 B2 Hbs. slia0.
            -- assert (Hne2 : t2 <> t) by (intros E; apply Hne; rewrite E; reflexivity).
               assert (Hne2s : t2 <> (t + 1)%uint63) by (intros E; apply E2s; rewrite E; reflexivity).
               destruct (Hold t2 r2 Hne2 Hne2s Hi2) as (rg & Hrg2 & El & En). rewrite <- El, <- En.
               destruct (Hnewsep t2 rg Hrg2) as [[D|D] _]; [left | right]; clear - D A1 B1; slia0.
          * assert (Hne1t : t1 <> t) by (intros E; apply E1t; rewrite E; reflexivity).
            destruct (Z.eq_dec (to_Z t1) (to_Z (t + 1)%uint63)) as [E1s|E1s].
            -- apply to_Z_inj in E1s. subst t1.
               destruct (Enew (t + 1)%uint63 r1 (or_intror eq_refl) Hi1) as [(E & _)|(_ & A2 & B2)]; [exfalso; symmetry in E; exact (NE01 t eq_refl E)|].
               destruct (Z.eq_dec (to_Z t2) (to_Z t)) as [E2t|E2t].
               ++ apply to_Z_inj in E2t. subst t2.
                  destruct (Enew t r2 (or_introl eq_refl) Hi2) as [(_ & A1 & B1)|(E & _)]; [| exfalso; exact (NE01 t eq_refl E)].
                  clear - A1 B1 A2 B2 Hbs. slia0.
               ++ assert (Hne2 : t2 <> t) by (intros E; apply E2t; rewrite E; reflexivity).
                  assert (Hne2s : t2 <> (t + 1)%uint63) by (intros E; apply Hne; rewrite E; reflexivity).
                  destruct (Hold t2 r2 Hne2 Hne2s Hi2) as (rg & Hrg2 & El & En). rewrite <- El, <- En.
                  destruct (Hnewsep t2 rg Hrg2) as [_ [D|D]]; [left | right]; clear - D A2 B2; slia0.
            -- assert (Hne1s : t1 <> (t + 1)%uint63) by (intros E; apply E1s; rewrite E; reflexivity).
               destruct (Hold t1 r1 Hne1t Hne1s Hi1) as (q1 & Hq1 & El1 & En1). rewrite <- El1, <- En1.
               destruct (Z.eq_dec (to_Z t2) (to_Z t)) as [E2t|E2t].
               ++ apply to_Z_inj in E2t. subst t2.
                  destruct (Enew t r2 (or_introl eq_refl) Hi2) as [(_ & A1 & B1)|(E & _)]; [| exfalso; exact (NE01 t eq_refl E)].
                  destruct (Hnewsep t1 q1 Hq1) as [[D|D] _]; [right | left]; clear - D A1 B1; slia0.
               ++ destruct (Z.eq_dec (to_Z t2) (to_Z (t + 1)%uint63)) as [E2s|E2s].
                  ** apply to_Z_inj in E2s. subst t2.
                     destruct (Enew (t + 1)%uint63 r2 (or_intror eq_refl) Hi2) as [(E & _)|(_ & A2 & B2)]; [exfalso; symmetry in E; exact (NE01 t eq_refl E)|].
                     destruct (Hnewsep t1 q1 Hq1) as [_ [D|D]]; [right | left]; clear - D A2 B2; slia0.
                  ** assert (Hne2 : t2 <> t) by (intros E; apply E2t; rewrite E; reflexivity).
                     assert (Hne2s : t2 <> (t + 1)%uint63) by (intros E; apply E2s; rewrite E; reflexivity).
                     destruct (Hold t2 r2 Hne2 Hne2s Hi2) as (q2 & Hq2 & El2 & En2). rewrite <- El2, <- En2.
                     exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
        (* [comment removed for export] *)
        assert (TMA : forall x, x <> tm -> iget x (iset 0 (err_region K (t + 16) rg0 pe) (iset (t + 1) (sh_region false t n) (iset t (blk_region n lg iempty) (iset tm rgW (iset 1 (drop_below off rg1) (f_mem F)))))) = iget x TM).
        { intros x NE. subst TM. rewrite !iget_iset. rewrite (proj2 (Uint63.eqb_false_spec _ _) NE). reflexivity. }
        assert (HrgW : iget tm (iset 0 (err_region K (t + 16) rg0 pe) (iset (t + 1) (sh_region false t n) (iset t (blk_region n lg iempty) (iset tm rgW (iset 1 (drop_below off rg1) (f_mem F)))))) = Some rgW) by (rewrite !iget_iset, Htm0f, Htms, Htmt, Uint63.eqb_refl; reflexivity).
        assert (HrgmTM : iget tm TM = Some rgm1) by (subst TM; rewrite !iget_iset, Htm0f, Htms, Htmt; pose proof Hrgm1 as X1; rewrite iget_iset in X1; exact X1).
        assert (Erho''m : rho'' tm = wa Dm) by (rewrite Erho''old by exact Htm_lt; exact ErDm).
        (* [comment removed for export] *)
        assert (FOOTP : forall x r, iget x TM = Some r -> x <> tm ->
                  P + 8 <= bv_unsigned (rho'' x) + to_Z (rg_lo r) \/ bv_unsigned (rho'' x) + to_Z (rg_len r) <= P).
        { intros x r Hx NE. subst TM. rewrite !iget_iset in Hx.
          destruct (x =? 0)%uint63 eqn:E0.
          { apply Uint63.eqb_spec in E0. subst x. injection Hx as <-. unfold err_region. cbn [rg_lo rg_len]. rewrite Hrho''0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
            rewrite Hlen0. right. clear - HDmtop Hom0; subst P; slia0. }
          destruct (x =? t + 1)%uint63 eqn:Es.
          { apply Uint63.eqb_spec in Es. subst x. injection Hx as <-. unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq n) by (clear - Hn1 Hn32; slia0). change (to_Z 0%uint63) with 0. fold (nsh (to_Z n)).
            rewrite Erho''s. pose proof (sh_aapp_range Ab (to_Z n) R7 R3) as (Q1 & Q2 & Q3). pose proof (sh_above_image Ab ltac:(clear - R1; slia0)) as SAI.
            rewrite wa_unsigned by (clear - Q2 Q3 SAI R3 Hn1; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia0). clear - HfreshPS. slia0. }
          destruct (x =? t)%uint63 eqn:Et'.
          { apply Uint63.eqb_spec in Et'. subst x. injection Hx as <-. unfold blk_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. rewrite Erho''t, wa_unsigned by (clear - R1 R5 ACEILB Hn; slia0). clear - HfreshP. slia0. }
          destruct (x =? 1)%uint63 eqn:E1.
          { apply Uint63.eqb_spec in E1. subst x. injection Hx as <-. unfold drop_below. cbn [rg_lo rg_len]. rewrite Erho''1, Hlo1, Hlen1. change (to_Z 0%uint63) with 0.
            rewrite wa_unsigned by (clear - Hhl Hlsp HspB HB64 Hcs ACEILB; slia0).
            destruct (OBJFm (fun E => NE (eq_sym E))) as (Dce & _). left. clear - Dce RNGm Hhl Hlsp Hom0; subst P; slia0. }
          apply Uint63.eqb_false_spec in E1. apply Uint63.eqb_false_spec in E0.
          rewrite (Erho''old x (OLDLT _ _ Hx)).
          destruct (proj2 Hmem x tm r rgm NE Hx Hrgm) as [SEP|SEP]; rewrite ErDm, ?Hlodm in SEP;
            rewrite (wa_unsigned Dm) in SEP by (clear - HDm0 HDmhi Hldm; unfold AAPP_HI in HDmhi; slia0); rewrite ?Hlodm in SEP; change (to_Z 0%uint63) with 0 in SEP;
            [right; clear - SEP RNGm Hom0; subst P; slia0| left; clear - SEP RNGm Hom0; subst P; slia0]. }
        assert (MH2 : forall w : word, m' w = write_to_mem mH (adr rho'' tm (to_Z offm)) (wbytes8 (dv rho'' (FV t w_zero))) w).
        { intros w. rewrite (adr_eq_wa rho'' tm Dm (to_Z offm) Erho''m HDm0) by (first [clear - Hom0; slia0| clear - Hom0 HDmhi RNGm; unfold AAPP_HI in HDmhi; slia0]). fold P.
          rewrite (dv_tag_zero rho'' t) by (clear - Xn0a Xn0b Hn59; slia0). rewrite Erho''t.
          pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
          rewrite write_to_mem_spec by (rewrite ?length_wbytes8; clear - HP64; slia0). rewrite length_wbytes8. change (Z.of_nat 8) with 8.
          destruct (Z.leb_spec0 P (bv_unsigned w)) as [L1|L1]; [destruct (Z.ltb_spec0 (bv_unsigned w) (P + 8)) as [L2|L2]|]; cbn [andb].
          - rewrite <- (wa_id w). rewrite (wa_unsigned (bv_unsigned w)) by (clear - Hw; slia0). destruct HPcell as [[_ (_ & _ & BYP)] _]. cbn [cells_bytes cbytes app] in BYP. rewrite app_nil_r in BYP.
            rewrite <- (mrd_overlay_high m' (bv_unsigned w)) by (clear - L1 L2 HDmtop Hom0 HP64; subst P; slia0).
            replace (bv_unsigned w) with (P + Z.of_nat (Z.to_nat (bv_unsigned w - P))) at 1 by (clear - L1; slia0).
            rewrite BYP by (unfold le8, word_to_le_bytes; rewrite length_Z_to_le_bytes; clear - L1 L2; slia0).
            unfold le8, word_to_le_bytes, wbytes8, wa. reflexivity.
          - symmetry. apply MHw. clear - L2; slia0.
          - symmetry. apply MHw. clear - L1; slia0. }
        apply mem_ok_parts.
        + intros t' rg' Ht'. destruct (Uint63.eqb t' tm) eqn:Etm'.
          * apply Uint63.eqb_spec in Etm'. subst t'. rewrite HrgW in Ht'. injection Ht' as <-.
            pose proof (PARTSH tm rgm1 HrgmTM) as PH.
            destruct (write_cell_sound asegs IM rho'' _ tm offm (FV t w_zero) _ rgm1 mH HWC Hrgm1 PH Htm0 Gmunk Gminb ltac:(rewrite Gmlen; exact Hom) Hal8) as (_ & PW & _).
            apply (mem_part_transfer asegs IM rho'' (write_to_mem mH (adr rho'' tm (to_Z offm)) (wbytes8 (dv rho'' (FV t w_zero)))) m' tm rgW Dm Erho''m HDm0);
              [unfold rgW; cbn [wb_region rg_len]; rewrite Gmlen; clear - HDmhi; unfold AAPP_HI in HDmhi; slia0| intros a Ha; apply pw_keep; apply MH2| intros _ _ _; exact Htm0| exact PW].
          * apply Uint63.eqb_false_spec in Etm'. rewrite (TMA t' Etm') in Ht'. pose proof (PARTSH t' rg' Ht') as PH.
            pose proof (FOOTP t' rg' Ht' Etm') as FP.
            destruct (t' =? 0)%uint63 eqn:E0.
            -- apply Uint63.eqb_spec in E0. subst t'. pose proof Ht' as Ht0'. subst TM. rewrite !iget_iset in Ht0'.
               change ((0 =? 0)%uint63) with true in Ht0'. cbv iota in Ht0'. injection Ht0' as <-.
               apply (mem_part_transfer0 IMX rho'' mH m' (err_region K (t + 16) rg0 pe) Hrho''0); [unfold err_region; cbn [rg_len]; rewrite Hlen0; unfold AIMG_TOP; clear; slia0| | exact PH].
               intros a Ha. unfold err_region in Ha. cbn [rg_lo rg_len] in Ha. rewrite Hlo0, Hlen0 in Ha. apply pw_keep. symmetry. apply MHo; [clear - Ha; unfold AIMG_LO, AIMG_TOP in Ha; slia0| clear - Ha HDmtop Hom0; subst P; unfold AIMG_TOP in *; slia0].
            -- apply Uint63.eqb_false_spec in E0. pose proof (proj1 PH) as (_ & _ & RO3 & RO4 & _).
               apply (mem_part_transfer asegs IM rho'' mH m' t' rg' (bv_unsigned (rho'' t')));
                 [symmetry; apply wa_id| clear; pose proof (bv_unsigned_in_range 64 (rho'' t')); slia0| clear - RO3; slia0| | intros _ _ _; exact E0| exact PH].
               intros a Ha. apply pw_keep. symmetry. apply MHo; [pose proof (RO4 E0) as RO4'; clear - Ha RO3 RO4'; slia0| clear - Ha FP; slia0].
        + intros t1 t2 r1 r2 Hne Hi1 Hi2.
          assert (BK : forall x r, iget x (iset 0 (err_region K (t + 16) rg0 pe) (iset (t + 1) (sh_region false t n) (iset t (blk_region n lg iempty) (iset tm rgW (iset 1 (drop_below off rg1) (f_mem F)))))) = Some r -> exists r0, iget x TM = Some r0 /\ rg_lo r0 = rg_lo r /\ rg_len r0 = rg_len r).
          { intros x r Hx. destruct (Uint63.eqb x tm) eqn:E.
            - apply Uint63.eqb_spec in E. subst x. rewrite HrgW in Hx. injection Hx as <-. exists rgm1. split; [exact HrgmTM|]. unfold rgW. cbn [wb_region rg_lo rg_len]. split; reflexivity.
            - apply Uint63.eqb_false_spec in E. rewrite (TMA x E) in Hx. exists r. split; [exact Hx|]. split; reflexivity. }
          destruct (BK t1 r1 Hi1) as (q1 & Hq1 & Lo1 & Le1). destruct (BK t2 r2 Hi2) as (q2 & Hq2 & Lo2 & Le2).
          rewrite <- Lo1, <- Le1, <- Lo2, <- Le2. exact (SEPM t1 t2 q1 q2 Hne Hq1 Hq2).
    }
    (* [comment removed for export] *)
    assert (Hrg0M : iget 0%uint63 (f_mem F) = Some rg0).
    { revert Hrg0'. rewrite !iget_iset.
      destruct (0 =? t + 1)%uint63 eqn:E01; [apply Uint63.eqb_spec in E01; apply (f_equal to_Z) in E01; rewrite Et1 in E01; change (to_Z 0%uint63) with 0 in E01; clear - E01 Xn0a Xn0b; slia0|].
      destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; apply (f_equal to_Z) in Et0; change (to_Z 0%uint63) with 0 in Et0; clear - Et0 Xn0a Xn0b; slia0|].
      destruct (0 =? tm)%uint63 eqn:E0m; [apply Uint63.eqb_spec in E0m; exfalso; exact (Htm0 (eq_sym E0m))|].
      change ((0 =? 1)%uint63) with false. cbv iota. intros E; exact E. }
    rewrite Hrg0M in Hrg0_.
    assert (STK1 : forall lo hi, stk asegs (ms_mem ms) lo hi -> (forall a, lo <= a < hi -> aclient_addr H LB (bv_unsigned (rv rho F 2)) a) -> stk asegs m' lo hi).
    { intros lo hi Hs Hcl. pose proof Hs as (S0' & S1' & _).
      apply (stk_pres asegs m1).
      - apply (stk_keep (ms_mem ms) m1); [exact Hs| exact WM1|]. intros a Ha.
        destruct (Z.lt_ge_cases a P) as [L|L]; [left; apply M1o; rewrite wa_unsigned by (clear - Ha S0' S1'; slia0); clear - L; slia0|].
        destruct (Z.lt_ge_cases a (P + 8)) as [L'|L']; [| left; apply M1o; rewrite wa_unsigned by (clear - Ha S0' S1'; slia0); clear - L'; slia0].
        right. subst m1. rewrite (mrd_overlay_high (write_to_mem (ms_mem ms) (wa P) (le8 (Z_to_bv 64 Ab))) a) by (clear - L L' HDmtop Hom0 HP64; subst P; slia0).
        rewrite write_to_mem_spec by (unfold le8, word_to_le_bytes; rewrite ?length_Z_to_le_bytes; clear - HP64; slia0). unfold le8, word_to_le_bytes. rewrite length_Z_to_le_bytes.
        rewrite wa_unsigned by (clear - L L' HP64; slia0). change (Z.of_nat 8) with 8.
        destruct (Z.leb_spec0 P a); [| exfalso; clear - L n0; slia0]. destruct (Z.ltb_spec0 a (P + 8)); [| exfalso; clear - L' n0; slia0]. cbn [andb].
        destruct (nth_error (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 Ab))) (Z.to_nat (a - P))) as [b|] eqn:En; [exists b; reflexivity|].
        exfalso. apply nth_error_None in En. rewrite length_Z_to_le_bytes in En. clear - En L L'. slia0.
      - intros a Ha. apply Hpres; [clear - Ha S0' S1'; slia0| exact (Hcl a Ha)]. }
    assert (GDJP : forall g, In g G -> disjoint_from [(P, P + 8)] (sh (g_addr g)) (nsh (to_Z (g_size g)))).
    { intros g Hg. pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (i63_range (g_size g)) as Hgs0.
      pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) B7 ltac:(clear - Hgs0; slia0)) as (U1 & U2 & U3).
      assert (SHA : sh aceil < aceil) by (clear - ACEILB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; slia0).
      cbn [disjoint_from]. split; [| exact I].
      destruct (Uint63.eqb tm 1) eqn:E1.
      - apply Uint63.eqb_spec in E1. destruct (STKm E1) as (_ & SPd & _). left. clear - U2 SHA SPd Hhl Hlsp Espu Hoff; subst P; slia0.
      - apply Uint63.eqb_false_spec in E1. destruct (OBJFm E1) as (_ & APD & _).
        destruct (app_vs_shX Dm (to_Z (rg_len rgm)) (g_addr g) (to_Z (g_size g)) APD ltac:(clear - Hldm; slia0) B7 ltac:(clear - Hgs0; slia0)) as [DD|DD];
          [right; clear - DD RNGm Hom0; subst P; slia0| left; clear - DD RNGm Hom0; subst P; slia0]. }
    assert (Ht0f : (t =? 0)%uint63 = false).
    { destruct (t =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. change (to_Z 0%uint63) with 0 in E. slia0. }
    assert (Hts0f : (t + 1 =? 0)%uint63 = false).
    { destruct (t + 1 =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. change (to_Z 0%uint63) with 0 in E. slia0. }
    assert (Htst : (t =? t + 1)%uint63 = false).
    { destruct (t =? t + 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. slia0. }
    assert (Ht1f : (t =? 1)%uint63 = false).
    { destruct (t =? 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. change (to_Z 1%uint63) with 1 in E. slia0. }
    assert (Hts1f : (t + 1 =? 1)%uint63 = false).
    { destruct (t + 1 =? 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. change (to_Z 1%uint63) with 1 in E. slia0. }
    pose proof (sh_aapp_range Ab (to_Z n) R7 R3) as (Q1 & Q2 & Q3).
    constructor; cbn [a_F a_n a_blk a_ff a_cost a_cnt a_cs mkc f_mem f_pc f_regs f_resv ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS ms1].
    - exact Evis'.
    - exact HRn'.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - subst rho'. rewrite rho_ext_old; [exact Xr0 | change (to_Z 0%uint63) with 0; slia0].
    - subst rho'. rewrite rho_ext_old; [exact Xr1 | change (to_Z 1%uint63) with 1; slia0].
    - subst rho'. rewrite rho_ext_old; [exact Xr2 | change (to_Z 2%uint63) with 2; slia0].
    - subst rho'. rewrite rho_ext_old; [exact Xr3 | change (to_Z 3%uint63) with 3; slia0].
    - eapply agree_trans; [exact Xag | exact Hag' | slia0].
    - rewrite Et17. slia0.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmpres').
    - exact Hheap'.
    - (* [comment removed for export] *) eapply (RFS_via_apres H HH); [| exact Hpres].
      eapply (ah_RFS_frame H HH); [exact Xrfs| exact MU1| exact WM1| apply Forall_cons; [exact AFDm| apply Forall_nil]].
    - exact Hac'.
    - (* [comment removed for export] *) pose proof (stack0_transport _ _ _ _ _ Xst0 MU1 WM1 ltac:(apply Forall_cons; [exact S0Dm| apply Forall_nil])) as Xst1.
      destruct Xst1 as (g & G1' & G2' & G3' & AD). exists g. split; [exact G1'|]. split; [exact G2'|]. split; [exact G3'|].
      destruct AD as [ADn SH]. split; [exact ADn|]. eapply (apres_SHAD H); [exact Hpres | exact SH |].
      (* [comment removed for export] *)
      do 6 right. rewrite shadow_of_length by slia0. pose proof (SHAD_aligned _ _ _ SH) as [_ G8].
      assert (M1 : sh aceil <= sh g) by (apply sh_mono; slia0).
      assert (M2 : sh g + nsh (q_shi Q - g) <= AHI_LO).
      { clear - G1' G2' G8. unfold nsh, sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia0. }
      slia0.
    - (* [comment removed for export] *) eapply (chain_via_apres H HH); [| exact Hpres |].
      + eapply (chain_via_munch H HH); [exact Xch| exact MU1|]. intros fp ra Hin. specialize (XCH0 fp ra Hin). cbn [disjoint_from]. split; [clear - XCH0 SP0Dm; subst P; slia0| exact I].
      + intros fp ra Hin. rewrite Espu. specialize (XCH0 fp ra Hin). clear - XCH0 Hhl Hlsp Hoff Hoff2 Hcs; slia0.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - (* [comment removed for export] *) exists (done ++ [(3%uint63, al, n)]). split; [rewrite Ecsq, Ecs, <- app_assoc; reflexivity | clear - HAL' HALs'; slia0].
    - exact XAL0.
    - (* [comment removed for export] *) cbn [map g_tag g_size]. rewrite XG. reflexivity.
    - (* [comment removed for export] *) constructor.
      + cbn [g_id g_addr g_size g_tag]. split; [left; reflexivity|]. split; [exact Erho't|]. split; [slia0|]. split; [slia0|]. split; [rewrite Et17; slia0|]. split.
        * exists (blk_region n lg iempty). rewrite !iget_iset. rewrite Ht0f, Htst, Uint63.eqb_refl. cbv iota.
          split; [reflexivity|]. unfold blk_region. cbn [rg_lo rg_len rg_kind rg_align]. repeat split; try reflexivity. clear - Hlg46; slia0.
        * intros rg' Hrg'. rewrite !iget_iset in Hrg'. rewrite Hts0f, Uint63.eqb_refl in Hrg'. cbv iota in Hrg'. injection Hrg' as <-.
          split; [reflexivity|]. split; [exact Erho's|]. cbn [g_addr g_size]. exact Had.
      + apply Forall_forall. intros g Hg.
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hsh).
        pose proof (i63_range (g_tag g)).
        assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia0).
        split; [right; exact Hin|]. split; [subst rho'; rewrite rho_ext_old by slia0; exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
        split; [rewrite Et17; slia0|]. split.
        * destruct (g_tag g =? tm)%uint63 eqn:Etm'.
          { (* [comment removed for export] *)
            apply Uint63.eqb_spec in Etm'. exists rgW. rewrite Etm', !iget_iset, Htm0f, Htms, Htmt, Uint63.eqb_refl. split; [reflexivity|].
            assert (Ergg : rgm1 = rgg).
            { pose proof Hrgm1 as X1. rewrite iget_iset in X1. rewrite <- Etm' in X1.
              destruct (g_tag g =? 1)%uint63 eqn:E1'; [apply Uint63.eqb_spec in E1'; exfalso; pose proof (f_equal to_Z E1'); change (to_Z 1%uint63) with 1 in *; slia0|].
              rewrite Hgg in X1. injection X1 as E. exact (eq_sym E). }
            unfold rgW. cbn [wb_region rg_lo rg_len rg_kind rg_align rg_dflt]. rewrite Ergg. repeat split; assumption. }
          exists rgg. rewrite !iget_iset.
          destruct (g_tag g =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); change (to_Z 0%uint63) with 0 in *; slia0|].
          destruct (g_tag g =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); slia0|].
          destruct (g_tag g =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; exfalso; pose proof (f_equal to_Z Et'); slia0|].
          rewrite Etm'.
          destruct (g_tag g =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); change (to_Z 1%uint63) with 1 in *; slia0|].
          split; [exact Hgg|]. repeat split; assumption.
        * intros rg' Hrg'. rewrite !iget_iset in Hrg'.
          destruct (g_tag g + 1 =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); rewrite Etg1 in *; change (to_Z 0%uint63) with 0 in *; slia0|].
          destruct (g_tag g + 1 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); rewrite Etg1, Et1 in *; slia0|].
          destruct (g_tag g + 1 =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; exfalso; pose proof (f_equal to_Z Et'); rewrite Etg1 in *; slia0|].
          rewrite (proj2 (Uint63.eqb_false_spec _ _) (TMG g Hg)) in Hrg'.
          destruct (g_tag g + 1 =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); rewrite Etg1 in *; change (to_Z 1%uint63) with 1 in *; slia0|].
          destruct (Hsh rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia0); exact Hrs|].
          eapply (apres_addressable H); [exact Hpres | | exact Hin]. eapply addressable_transport; [exact Had'| exact MU1| exact WM1| exact (GDJP g Hg)].
    - (* [comment removed for export] *) cbn [map g_id]. constructor; [|exact XGnd]. intros Hin. apply Hpfresh.
      apply in_map_iff in Hin as (g & <- & Hg). exact (HGids g Hg).
    - (* [comment removed for export] *) cbn [map g_tag]. constructor; [|exact XGtnd]. intros Hin.
      apply in_map_iff in Hin as (g & E & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _).
      rewrite E in Htg2. slia0.
    - (* [comment removed for export] *) constructor.
      + right. cbn [g_addr g_size g_id g_tag]. split; [| split; [| clear - Xn0a Xn0b; cbn [q_n0] in *; slia0]].
        * intros a Hcl Hna. assert (Ha64 : 0 <= a < 2 ^ 64 \/ ~ (0 <= a < 2 ^ 64)) by slia0.
          destruct Ha64 as [Ha64|Ha64].
          -- split; [intros Hin; destruct (Hfresh a 1 (Hclient a Ha64 Hcl Hna) ltac:(slia0)); slia0
                   | intros Hin; destruct (HfreshS a 1 (Hclient a Ha64 Hcl Hna) ltac:(slia0)); slia0].
          -- pose proof (sh_above_image Ab ltac:(slia0)) as SAI. split; intros Hin; clear - Ha64 Hin R1 R5 Q2 Q3 SAI ACEILB; unfold AIMG_TOP, AHI_LO in *; slia0.
        * intros b Hb Hni E. apply Hpfresh. rewrite E. apply in_map. exact (XLB0 b Hb Hni).
      + exact XGnew.
    - (* [comment removed for export] *) constructor.
      + cbn [g_addr g_size]. pose proof (stk_of_rw_cells asegs m' Ab _ Hblk) as Hs. cbn [cells_size csize] in Hs.
        rewrite Nat.add_0_r, Z2Nat.id in Hs by slia0. exact Hs.
      + apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _ & Hsz & _).
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
        apply STK1; [exact Hs|]. intros a Ha.
        unfold aclient_addr. do 2 right. left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr blk_size fst snd]; clear - Ha; slia0].
    - (* [comment removed for export] *) exact XFF.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)).
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia0).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia0).
      split; [subst rho'; rewrite rho_ext_old by slia0; exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia0); exact Hf1|].
      split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; slia0); exact Hf2|]. split; [exact Hk|]. split; [exact Htg1|]. split; [rewrite Et17; slia0|].
      assert (NT : forall x, to_Z x = to_Z (f_tag f) \/ to_Z x = to_Z (f_tag f) + 1 \/ to_Z x = to_Z (f_tag f) + 2 ->
                   (x =? 0)%uint63 = false /\ (x =? t + 1)%uint63 = false /\ (x =? t)%uint63 = false /\ (x =? 1)%uint63 = false).
      { intros x Hx. repeat split;
          (destruct (Uint63.eqb x _) eqn:E; [|reflexivity]; apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; rewrite ?Et1 in E;
           change (to_Z 0%uint63) with 0 in E; change (to_Z 1%uint63) with 1 in E; exfalso; slia0). }
      destruct (NT (f_tag f) ltac:(left; reflexivity)) as (N0 & N1 & N2 & N3).
      destruct (NT (f_tag f + 1)%uint63 ltac:(right; left; exact Etg1)) as (M0 & M1' & M2' & M3).
      destruct (NT (f_tag f + 2)%uint63 ltac:(right; right; exact Etg2)) as (P0 & P1 & P2 & P3).
      destruct (TMF f Hf) as [TMs TMl].
      split.
      { rewrite !iget_iset, N0, N1, N2. destruct (f_tag f =? tm)%uint63 eqn:Etm'.
        - apply Uint63.eqb_spec in Etm'. exists rgW. split; [reflexivity|].
          assert (Ergf : rgm1 = rgf).
          { pose proof Hrgm1 as XR1. rewrite iget_iset in XR1. rewrite <- Etm', N3, Hgf in XR1. injection XR1 as E. exact (eq_sym E). }
          unfold rgW. cbn [wb_region rg_lo rg_len rg_kind rg_align rg_dflt]. rewrite Ergf. repeat split; assumption.
        - rewrite N3. exists rgf. split; [exact Hgf|]. repeat split; assumption. }
      split; [exists rgs; rewrite !iget_iset, M0, M1', M2', (proj2 (Uint63.eqb_false_spec _ _) TMs), M3; split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite !iget_iset, P0, P1, P2, (proj2 (Uint63.eqb_false_spec _ _) TMl), P3; exact Hflg|].
      repeat split; assumption.
    - exact XFFnd.
    - exact XFFtnd.
    - (* [comment removed for export] *) destruct XTsep as (S1 & S2 & S3). split; [|split; [|exact S3]].
      + intros g g' [<-|Hg] [<-|Hg'] Hne; cbn [g_tag].
        * exfalso. apply Hne. reflexivity.
        * pose proof (proj1 (Forall_forall _ _) XGin g' Hg') as (_ & _ & _ & _ & Htg2' & _). right. slia0.
        * pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2' & _). left. slia0.
        * exact (S1 g g' Hg Hg' Hne).
      + intros g f [<-|Hg] Hf; cbn [g_tag].
        * pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Hftg2 & _). right. slia0.
        * exact (S2 g f Hg Hf).
    - exact XFFlen.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; left; exact E0|].
      destruct (t' =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; do 5 right; left; cbn [map g_tag]; left; symmetry; exact Ets|].
      destruct (t' =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; do 4 right; left; cbn [map g_tag]; left; symmetry; exact Et'|].
      destruct (t' =? tm)%uint63 eqn:Etm'.
      { apply Uint63.eqb_spec in Etm'. subst t'. destruct (Xdom tm rgm Hrgm) as [H0' | [H1' | [H2' | [H3' | [Hb' | [Hbs' | Hf']]]]]];
        [left; exact H0' | right; left; exact H1' | do 2 right; left; exact H2' | do 3 right; left; exact H3'
        | do 4 right; left; cbn [map]; right; exact Hb' | do 5 right; left; cbn [map]; right; exact Hbs' | do 6 right; exact Hf']. }
      destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; right; left; exact E1|].
      destruct (Xdom t' rg' Ht') as [H0' | [H1' | [H2' | [H3' | [Hb' | [Hbs' | Hf']]]]]];
        [left; exact H0' | right; left; exact H1' | do 2 right; left; exact H2' | do 3 right; left; exact H3'
        | do 4 right; left; cbn [map]; right; exact Hb' | do 5 right; left; cbn [map]; right; exact Hbs' | do 6 right; exact Hf'].
    - (* [comment removed for export] *) assert (Erg0 : rg0 = rg0_) by (clear - Hrg0_; congruence). subst rg0_.
      exists (err_region K (t + 16) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len rg_dflt rg_pages]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0|].
      intros pn p' Hp'. rewrite iget_iset in Hp'. destruct (pn =? c_errcell K >> 12)%uint63 eqn:Epn.
      + apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_kind]. exact (Hpg0 _ _ Hpe).
      + exact (Hpg0 _ _ Hp').
    - (* [comment removed for export] *) rewrite !iget_iset. change ((1 =? 0)%uint63) with false.
      destruct (1 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets) as EE; rewrite Et1 in EE; change (to_Z 1%uint63) with 1 in EE; clear - EE Xn0a Xn0b; slia0|].
      destruct (1 =? t)%uint63 eqn:Et1'; [apply Uint63.eqb_spec in Et1'; exfalso; pose proof (f_equal to_Z Et1') as EE; change (to_Z 1%uint63) with 1 in EE; clear - EE Xn0a Xn0b; slia0|].
      destruct (1 =? tm)%uint63 eqn:E1m.
      + apply Uint63.eqb_spec in E1m. exists rgW. cbv iota. split; [reflexivity|].
        assert (Ergm : rgm1 = drop_below off rg1) by (pose proof Hrgm1 as X1; rewrite iget_iset, <- E1m, Uint63.eqb_refl in X1; injection X1 as E; symmetry; exact E).
        unfold rgW. cbn [wb_region rg_lo rg_len rg_dflt rg_kind rg_align]. rewrite Ergm. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
      + exists (drop_below off rg1). change ((1 =? 1)%uint63) with true. cbv iota. split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((2 =? 0)%uint63) with false.
      destruct (2 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); rewrite Et1 in *; change (to_Z 2%uint63) with 2 in *; slia0|].
      destruct (2 =? t)%uint63 eqn:Et2'; [apply Uint63.eqb_spec in Et2'; exfalso; pose proof (f_equal to_Z Et2'); change (to_Z 2%uint63) with 2 in *; slia0|].
      rewrite (proj2 (Uint63.eqb_false_spec _ _) (fun E => TM2 (eq_sym E))). change ((2 =? 1)%uint63) with false. exact Xreg2.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((3 =? 0)%uint63) with false.
      destruct (3 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); rewrite Et1 in *; change (to_Z 3%uint63) with 3 in *; slia0|].
      destruct (3 =? t)%uint63 eqn:Et3'; [apply Uint63.eqb_spec in Et3'; exfalso; pose proof (f_equal to_Z Et3'); change (to_Z 3%uint63) with 3 in *; slia0|].
      rewrite (proj2 (Uint63.eqb_false_spec _ _) (fun E => TM3 (eq_sym E))). change ((3 =? 1)%uint63) with false. exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0x & Hrg0x & Hroc).
      assert (rg0x = rg0) by (fold F in Hrg0x; clear - Hrg0x Hrg0M; congruence). subst rg0x.
      exists (err_region K (t + 16) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
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
             rewrite Z.mod_small in Hir by slia0.
             split; [Z.div_mod_to_equations; nia | split; [Z.div_mod_to_equations; nia | intros v Ev; injection Hc as Ec; rewrite Ev in Ec; unfold err_cell in Ec; discriminate Ec]].
          -- exact (Xinb 0%uint63 rg0 _ pe ci c Hrg0M Hpe Hc).
        * exact (Xinb 0%uint63 rg0 pn p' ci c Hrg0M Hp' Hc).
      + destruct (t' =? t + 1)%uint63 eqn:Ets.
        * (* [comment removed for export] *)
          injection Ht' as <-. unfold sh_region in Hp' |- *. cbn [rg_pages rg_len] in Hp' |- *. rewrite iget_iset, iget_iempty in Hp'.
          destruct (pn =? 0)%uint63 eqn:Epn; [|discriminate]. apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_cells] in Hc.
          pose proof (i63_range ci). destruct (sh_cells_inv n ci c ltac:(slia0) Hc) as [Hcilt ->].
          rewrite (nsh_eq n) by slia0. change (to_Z 0%uint63) with 0.
          split; [Z.div_mod_to_equations; slia0|]. split; [Z.div_mod_to_equations; slia0|].
          intros v Ev. unfold sh_cell in Ev. destruct (((ci + 1) * 8 <=? n >> 3))%uint63 eqn:Ecv; [|discriminate].
          apply (proj1 (leb8_spec ci n ltac:(slia0) ltac:(slia0))) in Ecv. Z.div_mod_to_equations. slia0.
        * destruct (t' =? t)%uint63 eqn:Et'.
          -- injection Ht' as <-. unfold blk_region in Hp'. cbn [rg_pages] in Hp'. rewrite iget_iempty in Hp'. discriminate.
          -- destruct (t' =? tm)%uint63 eqn:Etm'; [injection Ht' as <-; exact (INBW pn p' ci c Hp' Hc)|].
             destruct (t' =? 1)%uint63 eqn:E1.
             ++ injection Ht' as <-. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
                unfold drop_below. cbn [rg_len].
                unfold drop_page in Hc. cbn [fst snd] in Hc.
                destruct (pn =? off >> 12)%uint63.
                ** cbn [pg_cells] in Hc. destruct (keep_cells_ge_inv _ _ _ _ Hc) as [_ Hc']. fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc').
                ** fold F in Hrg1. exact (Xinb 1%uint63 rg1 pn p0 ci c Hrg1 Hp0 Hc).
             ++ exact (Xinb t' rg' pn p' ci c Ht' Hp' Hc).
    - (* [comment removed for export] *) intros t' rg' Ht' Ht'0. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|].
      destruct (t' =? t + 1)%uint63 eqn:Ets.
      + injection Ht' as <-. unfold sh_region. cbn [rg_dflt rg_pages]. split; [right; reflexivity|].
        intros pn p' Hp'. rewrite iget_iset, iget_iempty in Hp'. destruct (pn =? 0)%uint63; [injection Hp' as <-; reflexivity | discriminate].
      + destruct (t' =? t)%uint63 eqn:Et'.
        * injection Ht' as <-. unfold blk_region. cbn [rg_dflt rg_pages]. split; [left; reflexivity|]. intros pn p' Hp'. rewrite iget_iempty in Hp'. discriminate.
        * destruct (t' =? tm)%uint63 eqn:Etm'; [injection Ht' as <-; destruct UNKW as (_ & Hdu & Hku); split; [left; exact Hdu| exact Hku]|].
          destruct (t' =? 1)%uint63 eqn:E1.
          -- injection Ht' as <-. apply Uint63.eqb_spec in E1. subst t'. fold F in Hrg1.
             unfold drop_below. cbn [rg_dflt rg_pages]. split; [exact Hdu1|].
             intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
             unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hkd1 _ _ Hp0).
          -- exact (Xkinds t' rg' Ht' Ht'0).
    - (* [comment removed for export] *) cbn [lb_bytes fold_right blk_size snd]. fold (lb_bytes LB). rewrite Ecost. slia0.
    - (* [comment removed for export] *) cbn [length]. rewrite Ecnt. slia0.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q)); [exact Hstk' | | clear - Espu Hhl Hlsp Hoff Hoff2 Hcs; slia0].
      apply STK1; [exact Hstk_hi|]. intros a Ha. left. clear - Ha; slia0.
    - repeat split; assumption.
    - exact Haux'.
    - exact Hinv'.
    - rewrite EerrA in Herr'. pose proof (stk_of_rw_cells asegs m' (errA A) [C4 errv'] Herr') as Hs. cbn [cells_size csize] in Hs.
      replace (errA A + Z.of_nat 4) with (errA A + 4) in Hs by slia0. exact Hs.
    - (* [comment removed for export] *) exact (HSH0 _ Hac' Hinv').
    - intros b Hb Hni. right. exact (XLB0 b Hb Hni).
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - (* [comment removed for export] *) intros b [<- | Hb].
      + right. exists (GB t p Ab n). split; [left; reflexivity | reflexivity].
      + destruct (XLBsub b Hb) as [Hb0 | (g & Hg & ->)]; [left; exact Hb0 | right; exists g; split; [right; exact Hg | reflexivity]].
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      rewrite <- (M1o (wa a)) by (rewrite wa_unsigned by (clear - Ha; slia0); exact (EXDm a Hcl Hna Hnxs)).
      apply Hpres; [exact Ha | exact (Hclient_addr a Ha Hcl Hna)].
    - (* [comment removed for export] *) apply Forall_forall. intros f__ Hf__. pose proof (proj1 (Forall_forall _ _) XFFstk f__ Hf__) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf__) as [(KF1 & KF2 & KF3 & KF4 & KF5) (FB1 & FB2 & FB3 & FB4)].
      apply STK1; [exact HsF|]. intros a__ Ha__. unfold aclient_addr. do 4 right. left. clear - Ha__ KF2 KF3; unfold AFS_HDR in *; slia0.
  Qed.
End NodeA.
