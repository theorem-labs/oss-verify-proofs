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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition aimg8_b (c : Z) : bool :=
  ((0x571000 <=? c) && (c + 8 <=? 0x5ea848)) || ((0x5ed1a0 <=? c) && (c + 8 <=? 0x673c00)) || ((0x6a7248 <=? c) && (c + 8 <=? 0x6a7298))
  || ((0xbccf50 <=? c) && (c + 8 <=? 0xc03570)).
Lemma aimg8_b_spec : forall c a, aimg8_b c = true -> c <= a < c + 8 -> aimg_client a.
Proof. intros c a Hb Ha. unfold aimg8_b in Hb. unfold aimg_client. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb. slia. Qed.

(* [comment removed for export] *)
Definition skb (b : byte) : slot := SK (of_Z (bv_unsigned b)).
Definition pin_cell_c4 (w : word) : cell :=
  match le4 w with [b0; b1; b2; b3] => CB (SL (skb b0) (skb b1) (skb b2) (skb b3) SU SU SU SU) | _ => CU end.
Definition aconst_pin_b (a : int) (cc : cell) : bool :=
  existsb (fun ac : Z * list Cells.cell =>
             ((fst ac =? to_Z a)%Z) && match snd ac with [C4 w] => cell_eqb cc (pin_cell_c4 w) | _ => false end) aconst_cells.

Lemma slot_eqb_eq : forall a b, slot_eqb a b = true -> a = b.
Proof.
  intros [x|v j|] [y|v' j'|] Hb; cbn in Hb; try discriminate; try reflexivity.
  - apply ho_eqb_eq in Hb. subst. reflexivity.
  - apply andb_true_iff in Hb as [H1 H2]. apply fval_eqb_eq in H1. apply ho_eqb_eq in H2. subst. reflexivity.
Qed.
Lemma cell_eqb_eq : forall a b, cell_eqb a b = true -> a = b.
Proof.
  intros [v| |sl] [v'| |sl'] Hb; cbn [cell_eqb] in Hb; try discriminate; try reflexivity.
  - apply fval_eqb_eq in Hb. subst. reflexivity.
  - destruct sl as [a0 a1 a2 a3 a4 a5 a6 a7], sl' as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold slots_eqb in Hb. cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7] in Hb.
    rewrite !andb_true_iff in Hb. destruct Hb as [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7].
    apply slot_eqb_eq in H0, H1, H2, H3, H4, H5, H6, H7. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ro_okb_sound : forall (K : i2consts) M rg0 (a : int) cc pn p ci c,
  ro_okb K M = true -> iget 0%uint63 M = Some rg0 -> In (a, cc) (c_ro K) ->
  iget pn (rg_pages rg0) = Some p -> iget ci (pg_cells p) = Some c ->
  to_Z pn * 4096 + to_Z ci * 8 = to_Z a -> 0 <= to_Z ci < 512 -> c = cc.
Proof.
  intros K M rg0 a cc pn p ci c Hok Hrg0 Hin Hp Hc Ea Hci. unfold ro_okb in Hok. rewrite Hrg0 in Hok.
  rewrite forallb_forall in Hok. specialize (Hok _ Hin). cbn [fst snd] in Hok.
  pose proof (i63_range pn). pose proof (i63_range ci). pose proof (i63_range a).
  assert (Epn : (a >> 12)%uint63 = pn).
  { apply to_Z_inj. rewrite to_Z_lsr12. slia. }
  assert (Eci : ((a land 4095) >> 3)%uint63 = ci).
  { apply to_Z_inj. rewrite to_Z_lsr3, to_Z_land4095. slia. }
  rewrite Epn, Hp, Eci, Hc in Hok. exact (cell_eqb_eq _ _ Hok).
Qed.

(* [comment removed for export] *)
Lemma aconst_pin_sound : forall m (a : int) cc, ACONST m -> aconst_pin_b a cc = true ->
  exists sl, cc = CB sl /\ forall (rho : int -> word) (j : int), 0 <= to_Z j < 8 ->
    slot_val rho (sget j sl) (rview asegs m (wa (to_Z a + to_Z j))).
Proof.
  intros m a cc Hac Hb. unfold aconst_pin_b in Hb. apply existsb_exists in Hb as ([a0 cs] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_true_iff in Hb as [Ha Hcs]. apply Z.eqb_eq in Ha.
  destruct cs as [|c0 [|c1 l]]; [discriminate | | destruct c0; discriminate]. destruct c0 as [w|w|w|b8_|nn bs]; try discriminate.
  apply cell_eqb_eq in Hcs. subst cc. unfold pin_cell_c4.
  pose proof (length_le4 w) as Hl4.
  destruct (le4 w) as [|b0 [|b1 [|b2 [|b3 [|b4 l4]]]]] eqn:E4; cbn in Hl4; try discriminate.
  eexists. split; [reflexivity|]. intros rho j Hj.
  pose proof (proj1 (Forall_forall _ _) (proj1 Hac) _ Hin) as R. cbn [fst snd] in R. rewrite Ha in R.
  destruct R as [[_ (_ & _ & HB)] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r, E4 in HB. cbn [length] in HB.
  assert (Hsk : forall (b : byte) (k : nat), (k < 4)%nat -> nth_error [b0; b1; b2; b3] k = Some b ->
            slot_val rho (skb b) (rview asegs m (wa (to_Z a + Z.of_nat k)))).
  { intros b k Hk Hn. unfold skb. cbn [slot_val]. change (rview asegs m (wa (to_Z a + Z.of_nat k))) with (mrd asegs m (wa (to_Z a + Z.of_nat k))).
    rewrite (HB k Hk), Hn. f_equal. pose proof (bv_unsigned_in_range 8 b) as Hb8. change (bv_modulus 8) with 256 in Hb8.
    rewrite toZ_of_Z_small by slia. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hb8. }
  destruct (int_cases8 j Hj) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - change (sget 0%uint63 _) with (skb b0). exact (Hsk b0 0%nat ltac:(lia) eq_refl).
  - change (sget 1%uint63 _) with (skb b1). exact (Hsk b1 1%nat ltac:(lia) eq_refl).
  - change (sget 2%uint63 _) with (skb b2). exact (Hsk b2 2%nat ltac:(lia) eq_refl).
  - change (sget 3%uint63 _) with (skb b3). exact (Hsk b3 3%nat ltac:(lia) eq_refl).
  - change (sget 4%uint63 _) with SU. exact I.
  - change (sget 5%uint63 _) with SU. exact I.
  - change (sget 6%uint63 _) with SU. exact I.
  - change (sget 7%uint63 _) with SU. exact I.
Qed.

Section NodeM.
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

  (* [comment removed for export] *)
  Definition ro_const : Prop :=
    forall m m', ACONST m -> ACONST m' -> mem_inv asegs m -> mem_inv asegs m' ->
      forall a c, In (a, c) (c_ro K) -> aimg8_b (to_Z a) = false -> aconst_pin_b a c = false -> forall j, 0 <= j < 8 ->
        rview asegs m' (wa (to_Z a + j)) = rview asegs m (wa (to_Z a + j)).
  Hypothesis HROC : ro_const.

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

  Lemma csum_nonneg : forall l : list (int * int * int), 0 <= csum H l.
  Proof.
    pose proof (ah_costs H HH) as (C1 & _ & C3 & _).
    induction l as [|[[k a] b] l IH]; cbn [csum fold_right]; [slia|]. fold (csum H l).
    assert (0 <= cost1 H (k, a, b)); [|slia].
    unfold cost1. pose proof (i63_range a). pose proof (i63_range b).
    destruct (k =? 0)%uint63; [apply C1; slia|]. destruct (k =? 1)%uint63; [apply C3; slia|].
    destruct (k =? 2)%uint63; [pose proof (C1 (to_Z b) ltac:(slia)); pose proof (C3 (to_Z a) ltac:(slia)); slia | apply C1; slia].
  Qed.

  Lemma pop_cost_inv : forall k a b cs cs', pop_cost k a b cs = Some cs' -> cs = (k, a, b) :: cs'.
  Proof.
    intros k a b [|[[k' a'] b'] r] cs' Hp; cbn in Hp; [discriminate|].
    destruct ((k' =? k) && (a' =? a) && (b' =? b))%uint63 eqn:E; [|discriminate]. injection Hp as <-.
    rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3].
    apply Uint63.eqb_spec in E1. apply Uint63.eqb_spec in E2. apply Uint63.eqb_spec in E3. subst. reflexivity.
  Qed.

  Lemma call_sp_n_inv : forall stack F off, call_sp_n K stack F = Some off ->
    FxState.rget F 2 = FV 1 (W64 0 off)
    /\ (to_Z stack <= to_Z off)%Z /\ (to_Z off <= to_Z (c_stack K))%Z /\ (to_Z off mod 16 = 0)%Z.
  Proof.
    intros stack F off Hc. unfold call_sp_n in Hc. destruct (FxState.rget F 2) as [t [top o]].
    destruct ((t =? 1) && (top =? 0) && (stack <=? o) && (o <=? c_stack K) && (o land 15 =? 0))%uint63 eqn:E; [|discriminate].
    injection Hc as ->. rewrite !andb_true_iff in E. destruct E as [[[[E1 E2] E3] E4] E5].
    apply Uint63.eqb_spec in E1. apply Uint63.eqb_spec in E2. subst.
    apply Uint63.leb_spec in E3. apply Uint63.leb_spec in E4.
    apply Uint63.eqb_spec in E5. apply (f_equal to_Z) in E5.
    rewrite (i63_land_ones off 15%uint63 4 eq_refl ltac:(slia)) in E5. change (to_Z 0) with 0%Z in E5. change (2 ^ 4)%Z with 16%Z in E5.
    repeat split; try assumption; reflexivity.
  Qed.

  Lemma call_okn_inv : forall stack st off l, call_okn K stack st = Some (off, l) ->
    call_sp_n K stack (a_F st) = Some off /\ call_link (a_F st) = Some l
    /\ tp_ok K (a_F st) = true /\ resv_none (a_F st) = true /\ err_page_ok K (f_mem (a_F st)) = true
    /\ (to_Z (a_n st) < to_Z two59)%Z /\ (2 <= to_Z (a_n st))%Z.
  Proof.
    intros stack st off l Hc. unfold call_okn in Hc.
    destruct (call_sp_n K stack (a_F st)) as [off'|] eqn:E1; [|discriminate].
    destruct (call_link (a_F st)) as [l'|] eqn:E2; [|discriminate].
    destruct (tp_ok K (a_F st) && resv_none (a_F st) && err_page_ok K (f_mem (a_F st)) && (a_n st <? two59) && (2 <=? a_n st))%uint63 eqn:E; [|discriminate].
    injection Hc as -> ->. rewrite !andb_true_iff in E. destruct E as [[[[E3 E4] E5] E6] E7].
    apply Uint63.ltb_spec in E6. apply Uint63.leb_spec in E7. change (to_Z 2) with 2%Z in E7.
    repeat split; assumption || reflexivity.
  Qed.

  Theorem anode_malloc_sound : forall Q st st' rho msF mo,
    anode_malloc A st = Some st' ->
    to_Z (f_pc (a_F st)) = AMALLOC_STUB ->
    cells0_in A (f_mem (a_F st)) ->
    I2RA H IMX A Q st rho msF mo ->
    as_SR H (fun c' => exists rho', I2RA H IMX A Q st' rho' (cfg_ms c') (cfg_model c')) (mkCfg msF mo).
  Proof.
    intros Q st st' rho msF mo Hnode Hpc Hc0 (s & LB & G & FF & XS & ms & X).
    (* [comment removed for export] *)
    unfold anode_malloc in Hnode.
    destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) 10)) as [n|] eqn:Ha0; [|discriminate].
    destruct (pop_cost 0 n 0 (a_cs st)) as [cs|] eqn:Hpop; [|discriminate].
    match type of Hnode with (if ?b then _ else _) = _ => destruct b eqn:Hguard; [|discriminate] end.
    destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
    destruct (set_errno K (a_n st + 16)%uint63 (iset (a_n st + 1)%uint63 (sh_region false (a_n st) n) (iset (a_n st) (blk_region n 4 iempty) M1))) as [M2|] eqn:HM2; [|discriminate].
    injection Hnode as <-.
    destruct (call_okn_inv _ _ _ _ Hco) as (Hsp & Hlk & Htp & Hrv & Hep & Hn59 & Hn2).
    destruct (call_sp_n_inv _ _ _ Hsp) as (Esp2 & Hoff1 & Hoff2 & Hoff16).
    destruct (call_link_inv _ _ Hlk) as (Era & Hl2 & Hl62).
    pose proof (tp_ok_inv _ _ Htp) as Etp. pose proof (resv_none_inv _ Hrv) as Eresv. pose proof (conc63_inv _ _ Ha0) as Ea0.
    pose proof (pop_cost_inv _ _ _ _ _ Hpop) as Ecs.
    rewrite !andb_true_iff in Hguard. destruct Hguard as [[[[[[[[Hn1 Hn32] Hc1] Hc2] Hc3] Hk1] Hk2] Hchain] Hrook].
    apply Uint63.leb_spec in Hn1. apply Uint63.leb_spec in Hn32. change (to_Z 1%uint63) with 1 in Hn1. change (to_Z 32768%uint63) with 32768 in Hn32.
    apply Uint63.leb_spec in Hc1. apply Uint63.leb_spec in Hc2. apply Uint63.leb_spec in Hc3.
    apply Uint63.leb_spec in Hk1. apply Uint63.leb_spec in Hk2.
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & Hrg1 & ->).
    destruct (set_errno_inv _ _ _ _ HM2) as (rg0 & pe & Hrg0' & Hpe & Hpew & ->).
    rewrite !iget_iset in Hrg0'.
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
    assert (Ea0v : rv rho F 10 = Z_to_bv 64 (to_Z n)).
    { rewrite Erv. change (of_Z 10) with 10%uint63. fold F in Ea0. rewrite Ea0. apply dv_conc63. exact Xr0. }
    assert (Erav : rv rho F 1 = Z_to_bv 64 (to_Z l)).
    { rewrite Erv. change (of_Z 1) with 1%uint63. fold F in Era. rewrite Era. apply dv_conc63. exact Xr0. }
    (* [comment removed for export] *)
    destruct (rw_c4_of_stk asegs _ _ Xerr) as [errv Herrv].
    assert (EerrA : bv_unsigned (rv rho F 4) + -164 = errA A).
    { rewrite Etpv. unfold errA. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      unfold ATP. rewrite Z.mod_small by slia. unfold AERRNO, ATP in Eerr. slia. }
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q) Xstk ltac:(rewrite Espu; slia)) as [Hstk_lo Hstk_hi].
    (* [comment removed for export] *)
    pose proof (i63_range (a_cost st)). pose proof (i63_range (c_cost K)). pose proof (i63_range n).
    pose proof (i63_range (a_cnt st)). pose proof (i63_range (c_cnt K)). destruct (HK_caps A HK) as (Hcap1 & Hcap2 & Hcap3).
    assert (Ecost : to_Z (a_cost st + n)%uint63 = to_Z (a_cost st) + to_Z n).
    { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    assert (Ecnt : to_Z (a_cnt st + 1)%uint63 = to_Z (a_cnt st) + 1).
    { rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. change wB with (2 ^ 63). slia. }
    rewrite Ecost in Hc1. rewrite Ecnt in Hk1.
    assert (Halloc : as_alloc_ok H s LB (to_Z n)).
    { apply (ah_alloc H HH s LB (ms_mem ms) (to_Z n) Xheap); slia. }
    (* [comment removed for export] *)
    destruct XAL as (done & Ecsq & HAL).
    assert (HCm : as_Cm H (to_Z n) <= as_AL H s /\ as_AL H s - as_Cm H (to_Z n) >= q_AL0 Q - csum H (done ++ [(0%uint63, n, 0%uint63)])).
    { rewrite Ecs in Ecsq. pose proof XAL0 as B0. rewrite Ecsq, csum_app in B0. cbn [csum fold_right] in B0. fold (csum H cs) in B0.
      unfold cost1 in B0. change ((0 =? 0)%uint63) with true in B0. cbv iota in B0.
      pose proof (csum_nonneg cs). rewrite csum_app. cbn [csum fold_right]. unfold cost1. change ((0 =? 0)%uint63) with true. cbv iota. slia. }
    destruct HCm as [HCm HAL'].
    (* [comment removed for export] *)
    destruct (chain_okb_trace H IMX A HK HHx Hpfc _ _ _ _ _ _ _ _ _ _ _ _ _ X Hchain) as (CH & Hch & Htr).
    assert (Es0 : rv rho F 8 = Z_to_bv 64 (bv_unsigned (dv rho (FxState.rget F 8)))).
    { rewrite Erv. change (of_Z 8) with 8%uint63. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    (* [comment removed for export] *)
    assert (Hpc0 : to_Z (ka_pc0m A) = APC0_MALLOC).
    { destruct (HK_parts A HK) as (_ & _ & Hpcs & _). unfold K_pcs_ok in Hpcs. rewrite !andb_true_iff in Hpcs.
      destruct Hpcs as [[[_ Hm] _] _]. apply Z.eqb_eq in Hm. exact Hm. }
    rewrite Hpc0 in Htr.
    assert (Hral : bv_unsigned (rv rho F 1) = to_Z l).
    { rewrite Erav, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). pose proof (i63_range l). apply Z.mod_small. slia. }
    rewrite <- Hral in Htr.
    assert (Hch8 : as_chain H (ms_mem ms) (bv_unsigned (rv rho F 8)) CH) by exact Hch.
    eapply (ah_mono H HH).
    { eapply ((ah_malloc H HH) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q_F Q) (q_fc Q) msF (ms_mem ms) s LB (to_Z n) (q_lo Q) (q_B Q) errv mo CH).
      - rewrite <- Ems. exact Xvis.
      - exact Xheap.
      - exact Xak.
      - exact Halloc.
      - exact HCm.
      - exact Xaux.
      - rewrite Espu. slia.
      - exact Hstk_lo.
      - slia.
      - rewrite Espu. unfold AMALLOC_STACK in *. slia.
      - rewrite EerrA. exact Herrv.
      - exact Xinv.
      - exact Etpv.
      - rewrite Espu. clear - Hoff16 Hsp32 Hsp16 Hcs Hoff Est16. Z.div_mod_to_equations. slia.
      - exact Xac.
      - exact Hch8.
      - exact Htr.
      - exact Ea0v.
      - slia. }
    (* [comment removed for export] *)
    intros [msF' mo'] Hpost. unfold malloc_post in Hpost. cbn [cfg_ms cfg_model] in Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ab & junk & p & s'
                       & Evis' & Hak' & Hmpres' & Hinv' & Hstk' & Herr' & Haux' & Hpres & Hrng & Hheap' & Hblk & Had & Hac' & HALs').
    cbn [cfg_ms cfg_model].
    set (L17 := [wa Ab; wa (sh Ab); t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6'; errv']).
    set (rho' := rho_ext rho t L17).
    exists rho'.
    pose proof (i63_range t) as Ht.
    change (to_Z two59) with (2 ^ 59) in Hn59.
    assert (Hag' : agree t rho rho') by (apply agree_ext; [slia | slia | exact Xr0]).
    assert (Et17 : to_Z (t + 17)%uint63 = to_Z t + 17) by (rewrite to_Z_add_small; change (to_Z 17%uint63) with 17; slia).
    assert (Et16 : to_Z (t + 16)%uint63 = to_Z t + 16) by (rewrite to_Z_add_small; change (to_Z 16%uint63) with 16; slia).
    assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
    assert (Et2 : to_Z (t + 2)%uint63 = to_Z t + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
    pose proof Hrng as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    assert (EL17 : forall x (k : nat), (k < 17)%nat -> to_Z x = to_Z t + Z.of_nat k -> rho' x = nth k L17 w0).
    { intros x k Hk Hx. subst rho'. apply (rho_ext_at rho t L17 x k); [subst L17; cbn; slia | exact Hx]. }
    assert (Erho't : rho' t = wa Ab) by (rewrite (EL17 t 0%nat); [reflexivity | slia | slia]).
    assert (Erho's : rho' (t + 1)%uint63 = wa (sh Ab)) by (rewrite (EL17 _ 1%nat); [reflexivity | slia | rewrite Et1; slia]).
    assert (Erho'e : rho' (t + 16)%uint63 = errv') by (rewrite (EL17 _ 16%nat); [reflexivity | slia | rewrite Et16; slia]).
    (* [comment removed for export] *)
    assert (Hfresh : forall a k, aclient_range H LB (bv_unsigned (rv rho F 2)) a k -> 0 < k -> a + k <= Ab \/ Ab + to_Z n <= a).
    { intros a k Hr Hk. eapply (new_block_apart H HHx); [exact Hheap' | exact Hr | rewrite Espu; slia | exact Hk]. }
    assert (HfreshS : forall a k, aclient_range H LB (bv_unsigned (rv rho F 2)) a k -> 0 < k -> a + k <= sh Ab \/ sh Ab + nsh (to_Z n) <= a).
    { intros a k Hr Hk. eapply (new_shadow_apart H HHx); [exact Hheap' | exact Hr | rewrite Espu; slia | exact Hk]. }
    (* [comment removed for export] *)
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
    pose proof (ah_nodup H HH _ _ _ Hheap') as Hnd'. cbn [map blk_id fst] in Hnd'.
    pose proof (proj1 (NoDup_cons_iff _ _) Hnd') as [Hpfresh HndLB].
    assert (HGids : forall g, In g G -> In (g_id g) (map blk_id LB)).
    { intros g Hg. pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _).
      replace (g_id g) with (blk_id (g_id g, g_addr g, to_Z (g_size g))) by reflexivity. apply in_map. exact Hin. }
    (* [comment removed for export] *)
    assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> aclient_addr H LB (bv_unsigned (rv rho F 2)) a ->
                     rview asegs m' (wa a) = rview asegs (ms_mem ms) (wa a)
                     /\ (wview asegs (ms_mem ms) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hc. destruct (Hpres a Ha Hc) as [E W]. split; [apply rview_eq_of_mem; exact E | exact W]. }
    set (ms1 := MS (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 Ab)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6') (q_F Q) (ret_pc (rv rho F 1)) (q_fc Q) None m' (seg_rom asegs)).
    exists s', ((p, Ab, to_Z n) :: LB), (GB t p Ab n :: G), FF, XS, ms1.
    assert (HRn' : Rn asegs IM (t + 17)%uint63 rho'
              (FS (ret_of l) (iset 10 (FV t w_zero) (clobber clob14 (t + 2) (f_regs F)))
                  (iset 0 (err_region K (t + 16) rg0 pe) (iset (t + 1) (sh_region false t n) (iset t (blk_region n 4 iempty) (iset 1 (drop_below off rg1) (f_mem F))))) None)
              ms1).
    { intros rho'' Hag''. subst ms1.
      assert (HagF : agree t rho rho'') by (eapply agree_trans; [exact Hag' | exact Hag'' | rewrite Et17; slia]).
      pose proof (XRn rho'' HagF) as HR''. rewrite Ems in HR''.
      assert (Erho'' : forall x, to_Z x < to_Z t + 17 -> rho'' x = rho' x) by (intros x Hx; apply (proj2 Hag''); rewrite Et17; exact Hx).
      assert (Hrho''0 : rho'' 0%uint63 = Z_to_bv 64 0) by exact (proj1 Hag'').
      assert (Erho''t : rho'' t = wa Ab) by (rewrite Erho'' by slia; exact Erho't).
      assert (Erho''s : rho'' (t + 1)%uint63 = wa (sh Ab)) by (rewrite Erho'' by (rewrite Et1; slia); exact Erho's).
      assert (Erho''old : forall x, to_Z x < to_Z t -> rho'' x = rho x).
      { intros x Hx. rewrite Erho'' by slia. subst rho'. apply rho_ext_old. exact Hx. }
      assert (Erho''1 : rho'' 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K))) by (rewrite Erho''old by (change (to_Z 1%uint63) with 1; slia); exact Xr1).
      pose proof (R_mem _ _ _ _ _ HR'') as Hmem''. cbn [f_mem ms_mem] in Hmem''.
      constructor.
      - (* [comment removed for export] *) cbn [ms_pc_val f_pc]. rewrite Erav. apply ret_pc_of_link. exact Hl2.
      - (* [comment removed for export] *)
        change (Frame.mkR (rv rho F 1) (rv rho F 2) (rv rho F 3) (rv rho F 4) t0' t1' t2' (rv rho F 8) (rv rho F 9) (Z_to_bv 64 Ab)
                     a1' a2' a3' a4' a5' a6' a7' (rv rho F 18) (rv rho F 19) (rv rho F 20) (rv rho F 21) (rv rho F 22) (rv rho F 23)
                     (rv rho F 24) (rv rho F 25) (rv rho F 26) (rv rho F 27) t3' t4' t5' t6')
          with (mkRl [rv rho F 1; rv rho F 2; rv rho F 3; rv rho F 4; t0'; t1'; t2'; rv rho F 8; rv rho F 9; Z_to_bv 64 Ab;
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
        { intros k. apply iget_clobber; [exact Hnd14 | rewrite Et2; cbn [length clob14]; slia]. }
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
              rewrite (EL17 (of_Z (to_Z t1 + Z.of_nat i)) (S (S i))); [reflexivity | slia | rewrite Etag; slia]
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
        { revert Hrg0'.
          destruct (0 =? t + 1)%uint63 eqn:E01; [apply Uint63.eqb_spec in E01; apply (f_equal to_Z) in E01; rewrite Et1 in E01; change (to_Z 0%uint63) with 0 in E01; slia|].
          destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; apply (f_equal to_Z) in Et0; change (to_Z 0%uint63) with 0 in Et0; slia|].
          change ((0 =? 1)%uint63) with false. cbv iota. intros E; exact E. }
        destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0). fold F in Hrg0_. rewrite Hrg0M in Hrg0_. injection Hrg0_ as <-.
        destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
        (* [comment removed for export] *)
        assert (Hnewsep : forall t' rg', iget t' (f_mem F) = Some rg' ->
                  (Ab + to_Z n <= bv_unsigned (rho'' t') + to_Z (rg_lo rg') \/ bv_unsigned (rho'' t') + to_Z (rg_len rg') <= Ab)
                  /\ (sh Ab + nsh (to_Z n) <= bv_unsigned (rho'' t') + to_Z (rg_lo rg') \/ bv_unsigned (rho'' t') + to_Z (rg_len rg') <= sh Ab)).
        { intros t' rg' Ht'. pose proof (sh_aapp_range Ab (to_Z n) R7 R3) as (Q1 & Q2 & Q3).
          pose proof (ah_fsb H HH _ _ _ Xheap) as (F1 & F2 & F3 & F4).
          destruct (Xdom t' rg' Ht') as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl]]]]]]]].
          - rewrite Hrg0M in Ht'. injection Ht' as <-. rewrite Hrho''0, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0.
            pose proof (sh_above_image Ab ltac:(slia)) as SAI. clear - SAI R4. unfold AIMG_TOP, AIMG_LO in *. slia.
          - rewrite Hrg1 in Ht'. injection Ht' as <-. rewrite Erho''1, Hlo1, Hlen1. change (to_Z 0%uint63) with 0.
            rewrite wa_unsigned by (clear - Hhl Hlsp HspB HB64 Hcs ACEILB; slia). clear - Q2 Q3 R5 Hhl Hlsp ACEILB. unfold AHI_LO in Q3. slia.
          - rewrite Xreg2 in Ht'. injection Ht' as <-. rewrite (Erho''old 2%uint63) by (change (to_Z 2%uint63) with 2; slia). rewrite Xr2.
            unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (c_stack K)) by slia. change (to_Z 0%uint63) with 0. fold (nsh (to_Z (c_stack K))).
            pose proof (stack0_bounds _ _ _ Xst0) as [SB1 SB2].
            assert (SR : sh aceil <= sh (q_sp0 Q - to_Z (c_stack K)) /\ sh (q_sp0 Q - to_Z (c_stack K)) + nsh (to_Z (c_stack K)) <= sh (q_sp0 Q)
                         /\ sh (q_sp0 Q) <= AHI_LO /\ AIMG_TOP <= sh (q_sp0 Q - to_Z (c_stack K))).
            { split; [apply sh_mono; slia|]. split; [| split].
              - clear - Hsp32 Hcs Est16. unfold nsh, sh. Z.div_mod_to_equations. slia.
              - clear - SB2 Hshi. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia.
              - apply sh_above_image. slia. }
            rewrite wa_unsigned by (clear - SR Hcs; unfold AIMG_TOP, AHI_LO, nsh in SR; Z.div_mod_to_equations; slia).
            destruct R7 as [[P1 P2]|[P1 P2]].
            + assert (TMP2 : 0 <= aceil < AAPP_HI) by (unfold AAPP_HI; slia). pose proof (sh_in_shadowland aceil TMP2) as SL.
              clear - SR Q1 Q2 Q3 P1 P2 SL R3. unfold ALOWSH_LO, AHI_LO in *. slia.
            + clear - SR Q1 Q2 Q3 P1 P2 R3. unfold AHI_LO in *. slia.
          - rewrite Xreg3 in Ht'. injection Ht' as <-. rewrite (Erho''old 3%uint63) by (change (to_Z 3%uint63) with 3; slia). rewrite Xr3, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
            unfold abs_region. cbn [rg_lo rg_len].
            destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] _].
            apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. rewrite Hslo, Hslen.
            destruct R7 as [[P1 P2]|[P1 P2]]; clear - P1 P2 R1 R3 Hslo Hslen ACEILB; unfold sh, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *; rewrite ASHADOW_BASE_val in *; Z.div_mod_to_equations; slia.
          - apply in_map_iff in Hb as (g & <- & Hg).
            pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
            rewrite Hgg in Ht'. injection Ht' as <-. rewrite Hlog, Hleng. change (to_Z 0%uint63) with 0.
            rewrite (Erho''old (g_tag g)) by slia. rewrite Hrg. pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
            rewrite wa_unsigned by (clear - G1 G3 G5 ACEILB; slia).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (g_addr g) (to_Z (g_size g))).
            { right; right; left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr blk_size fst snd]; slia]. }
            destruct (Hfresh _ _ CR ltac:(slia)) as [D1|D1]; destruct (HfreshS _ _ CR ltac:(slia)) as [D2|D2]; clear - D1 D2; slia.
          - apply in_map_iff in Hbs as (g & <- & Hg).
            pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & _ & Hsh). destruct (Hsh rg' Ht') as (-> & Hrs & _).
            pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _ & G7).
            unfold sh_region. cbn [rg_lo rg_len]. rewrite (nsh_eq (g_size g)) by (clear - G1 G5 ACEILB; slia). change (to_Z 0%uint63) with 0. fold (nsh (to_Z (g_size g))).
            pose proof (i63_range (g_tag g)).
            rewrite (Erho''old (g_tag g + 1)%uint63) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia). rewrite Hrs.
            pose proof (sh_aapp_range (g_addr g) (to_Z (g_size g)) G7 G3) as (U1 & U2 & U3). pose proof (sh_above_image (g_addr g) ltac:(slia)) as SAI.
            rewrite wa_unsigned by (clear - U2 U3 SAI G1 Hsz; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (sh (g_addr g)) (nsh (to_Z (g_size g)))).
            { right; right; right; left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr blk_size fst snd]; slia]. }
            assert (Kn : 0 < nsh (to_Z (g_size g))) by (clear - Hsz; unfold nsh; Z.div_mod_to_equations; slia).
            destruct (Hfresh _ _ CR Kn) as [D1|D1]; destruct (HfreshS _ _ CR Kn) as [D2|D2]; clear - D1 D2; slia.
          - apply in_map_iff in Hf as (f & <- & Hf).
            pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
            rewrite Hgf in Ht'. injection Ht' as <-. rewrite Hlof, Hlenf, (fsz_eq _ Hk). change (to_Z 0%uint63) with 0.
            rewrite (Erho''old (f_tag f)) by slia. rewrite Hf0.
            destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)) as FP.
            rewrite wa_unsigned by (clear - K2 K3 F1 F2 FP ACEILB; unfold AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (f_ff f) (AsIface.fsz (to_Z (f_k f)))).
            { do 4 right. left. unfold AFS_HDR in *. slia. }
            destruct (Hfresh _ _ CR ltac:(slia)) as [D1|D1]; destruct (HfreshS _ _ CR ltac:(slia)) as [D2|D2]; clear - D1 D2; slia.
          - apply in_map_iff in Hfs as (f & <- & Hf).
            pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
            rewrite Hgs in Ht'. injection Ht' as <-. rewrite Hlos, Hlens. change (to_Z 0%uint63) with 0.
            pose proof (i63_range (f_tag f)).
            rewrite (Erho''old (f_tag f + 1)%uint63) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia). rewrite Hf1.
            destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)) as FP.
            pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2].
            assert (B : AIMG_TOP <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) <= AAPP_HI) by (clear - K2 K3 F1 F2 ACEILB FP; unfold AIMG_TOP, AFS_HDR, AFS_SIZE, AAPP_HI in *; slia).
            pose proof (sh_above_image (f_ff f) ltac:(unfold AIMG_TOP in B; slia)) as SA1. pose proof (sh_nsh_high (f_ff f) (AsIface.fsz (to_Z (f_k f))) ltac:(unfold AIMG_TOP in B; slia) ltac:(slia) (proj2 B)) as SA2.
            rewrite wa_unsigned by (clear - B SA1 SA2 FP; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (sh (f_ff f)) (fshn (to_Z (f_k f)))).
            { do 5 right. left. pose proof (sh_mono (as_FSB H) (f_ff f) ltac:(unfold AFS_HDR in *; slia)).
              assert (sh (f_ff f) + fshn (to_Z (f_k f)) <= sh (as_FSB H + AFS_SIZE)).
              { rewrite E1. pose proof (frame_al8 H _ _ _ (conj K1 (conj K2 (conj K3 (conj K4 K5))))) as A8. clear - K3 A8 E2 FP. unfold nsh, sh. Z.div_mod_to_equations. slia. }
              slia. }
            assert (Kn : 0 < fshn (to_Z (f_k f))) by (rewrite E1; clear - FP; unfold nsh; Z.div_mod_to_equations; slia).
            destruct (Hfresh _ _ CR Kn) as [D1|D1]; destruct (HfreshS _ _ CR Kn) as [D2|D2]; clear - D1 D2; slia.
          - apply in_map_iff in Hfl as (f & <- & Hf).
            pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & _ & _ & Hflg & _).
            rewrite Hflg in Ht'. injection Ht' as <-. unfold flag_region. cbn [rg_lo rg_len]. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
            pose proof (i63_range (f_tag f)).
            rewrite (Erho''old (f_tag f + 2)%uint63) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia). rewrite Hf2.
            destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _].
            rewrite wa_unsigned by (clear - K5 F1 F2 ACEILB; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE, AIMG_TOP in *; slia).
            assert (CR : aclient_range H LB (bv_unsigned (rv rho F 2)) (f_fp f) 1).
            { do 4 right. left. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. slia. }
            destruct (Hfresh _ _ CR ltac:(slia)) as [D1|D1]; destruct (HfreshS _ _ CR ltac:(slia)) as [D2|D2]; clear - D1 D2; slia. }
        apply mem_ok_parts.
        + intros t' rg' Ht'. rewrite !iget_iset in Ht'.
          destruct (t' =? 0)%uint63 eqn:E0.
          * (* [comment removed for export] *) apply Uint63.eqb_spec in E0. subst t'. injection Ht' as <-.
            eapply (region0_part asegs IM rho'' Hrho''0 IMX eq_refl HIMX HWRX K (ms_mem ms) m' rg0 pe (t + 16)%uint63 errv'
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
            -- rewrite dv_tag_zero by (rewrite Et16; slia). rewrite Erho'' by (rewrite Et16; slia). exact Erho'e.
            -- exact Eerr8.
            -- exact Ebi.
            -- destruct (err_page_ok_inv _ _ Hep) as (rg0b & pb & Hrg0b & Hir & _). fold F in Hrg0b. rewrite Hrg0M in Hrg0b. injection Hrg0b as <-.
               unfold in_region in Hir. rewrite !andb_true_iff in Hir. destruct Hir as [[[Hob _] _] Hir]. apply Uint63.leb_spec in Hir.
               apply Uint63.ltb_spec in Hob. change (to_Z off_bound) with (2 ^ 62) in Hob.
               rewrite Uint63.add_spec in Hir. change (to_Z 8%uint63) with 8 in Hir. change wB with (2 ^ 63) in Hir.
               pose proof (i63_range (rg_len rg0)). rewrite Z.mod_small in Hir by slia. exact Hir.
            -- rewrite Hlen0. reflexivity.
          * destruct (t' =? t + 1)%uint63 eqn:Ets.
            -- (* [comment removed for export] *) apply Uint63.eqb_spec in Ets. subst t'. injection Ht' as <-.
               apply (sh_region_part IM rho'' Hrho''0 false m' t n Ab).
               ++ exact Erho''s.
               ++ rewrite Erho''t. apply wa_unsigned. slia.
               ++ slia.
               ++ slia.
               ++ clear - R5 ACEILB. unfold AAPP_HI. slia.
               ++ exact (proj2 Had).
            -- destruct (t' =? t)%uint63 eqn:Et'.
               ++ (* [comment removed for export] *) apply Uint63.eqb_spec in Et'. subst t'. injection Ht' as <-.
                  apply (blk_region_part asegs IM rho'' m' t n 4%uint63 Ab Erho''t).
                  ** intros E. pose proof (f_equal to_Z E). change (to_Z 0%uint63) with 0 in *. slia.
                  ** slia.
                  ** split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [clear - R5 ACEILB; slia | exact I].
                  ** change (2 ^ to_Z 4%uint63) with 16. exact R2.
                  ** change (to_Z 4%uint63) with 4. slia.
                  ** slia.
                  ** destruct Hblk as [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by slia. exact Hw.
               ++ destruct (t' =? 1)%uint63 eqn:E1.
                  ** (* [comment removed for export] *) apply Uint63.eqb_spec in E1. subst t'. injection Ht' as <-.
                     destruct (Xkinds 1%uint63 rg1 Hrg1 ltac:(intros E; discriminate E)) as [_ Hkd1].
                     apply (stack_part asegs IM rho'' (ms_mem ms) m' rg1 off (q_sp0 Q - to_Z (c_stack K)) (q_lo Q) (q_sp0 Q)).
                     --- exact Erho''1.
                     --- exact Hlo1.
                     --- exact Hd1.
                     --- exact Hkd1.
                     --- rewrite Hlen1. reflexivity.
                     --- rewrite Hlen1. slia.
                     --- clear - Hoff16 Hoff. Z.div_mod_to_equations. slia.
                     --- exact (mem_part_of _ _ _ _ _ _ _ Hmem'' Hrg1).
                     --- exact Xstk.
                     --- slia.
                     --- rewrite <- Espu. exact Hstk'.
                     --- intros a Ha. destruct Xstk as (_ & H64 & _). apply Hkeep; [slia | left; rewrite Espu; slia].
                  ** (* [comment removed for export] *)
                     assert (Hne0 : t' <> 0%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E0; discriminate).
                     assert (Hne1 : t' <> 1%uint63) by (intros E; subst t'; rewrite Uint63.eqb_refl in E1; discriminate).
                     apply (old_parts H IMX A HK HHx HSH0 _ _ _ _ _ _ _ _ _ _ _ rho'' m' LB (bv_unsigned (rv rho F 2)) [] t' rg' X).
                     --- intros x Hx. apply Erho''old. exact Hx.
                     --- exact Hkeep.
                     --- rewrite Espu. slia.
                     --- intros g Hg _. exact (proj1 (proj1 (Forall_forall _ _) XGin g Hg)).
                     --- intros b Hb. exact Hb.
                     --- exact Hac'.
                     --- exact Hinv'.
                     --- exact Ht'.
                     --- exact Hne0.
                     --- exact Hne1.
                     --- intros g _ [].
        + (* [comment removed for export] *)
          intros t1 t2 r1 r2 Hne Hi1 Hi2. rewrite !iget_iset in Hi1, Hi2.
          (* [comment removed for export] *)
          assert (Hold : forall t' rg', t' <> t -> t' <> (t + 1)%uint63 ->
                    (if (t' =? 0)%uint63 then Some (err_region K (t + 16) rg0 pe)
                     else if (t' =? t + 1)%uint63 then Some (sh_region false t n)
                     else if (t' =? t)%uint63 then Some (blk_region n 4 iempty)
                     else if (t' =? 1)%uint63 then Some (drop_below off rg1) else iget t' (f_mem F)) = Some rg' ->
                    exists rg, iget t' (f_mem F) = Some rg /\ rg_lo rg = rg_lo rg' /\ rg_len rg = rg_len rg').
          { intros t' rg' Hne' Hne'' Ht'.
            destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; subst t'; injection Ht' as <-; exists rg0; split; [exact Hrg0M | split; reflexivity]|].
            destruct (t' =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; congruence|].
            destruct (t' =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; congruence|].
            destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; subst t'; injection Ht' as <-; exists rg1; split; [exact Hrg1 | split; reflexivity]|].
            exists rg'. split; [exact Ht' | split; reflexivity]. }
          assert (Ht0f : (t =? 0)%uint63 = false).
          { destruct (t =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. change (to_Z 0%uint63) with 0 in E. slia. }
          assert (Hts0f : (t + 1 =? 0)%uint63 = false).
          { destruct (t + 1 =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. change (to_Z 0%uint63) with 0 in E. slia. }
          assert (Htst : (t =? t + 1)%uint63 = false).
          { destruct (t =? t + 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. slia. }
          (* [comment removed for export] *)
          assert (Enew : forall t' r', (t' = t \/ t' = (t + 1)%uint63) ->
                    (if (t' =? 0)%uint63 then Some (err_region K (t + 16) rg0 pe)
                     else if (t' =? t + 1)%uint63 then Some (sh_region false t n)
                     else if (t' =? t)%uint63 then Some (blk_region n 4 iempty)
                     else if (t' =? 1)%uint63 then Some (drop_below off rg1) else iget t' (f_mem F)) = Some r' ->
                    (t' = t /\ bv_unsigned (rho'' t') + to_Z (rg_lo r') = Ab /\ bv_unsigned (rho'' t') + to_Z (rg_len r') = Ab + to_Z n)
                    \/ (t' = (t + 1)%uint63 /\ bv_unsigned (rho'' t') + to_Z (rg_lo r') = sh Ab /\ bv_unsigned (rho'' t') + to_Z (rg_len r') = sh Ab + nsh (to_Z n))).
          { intros t' r' [-> | ->] Hr'.
            - rewrite Ht0f, Htst, Uint63.eqb_refl in Hr'. cbv iota in Hr'. injection Hr' as <-. left. unfold blk_region. cbn [rg_lo rg_len].
              change (to_Z 0%uint63) with 0. rewrite Erho''t, wa_unsigned by slia. repeat split; slia.
            - rewrite Hts0f, Uint63.eqb_refl in Hr'. cbv iota in Hr'. injection Hr' as <-. right. unfold sh_region. cbn [rg_lo rg_len].
              change (to_Z 0%uint63) with 0. rewrite (nsh_eq n) by slia. rewrite Erho''s.
              pose proof (sh_aapp_range Ab (to_Z n) R7 R3) as (Q1 & Q2 & Q3). pose proof (sh_above_image Ab ltac:(slia)) as SAI.
              rewrite wa_unsigned by (clear - Q2 Q3 SAI R3 Hn1; unfold AIMG_TOP, AHI_LO, nsh in *; Z.div_mod_to_equations; slia).
              repeat split; slia. }
          (* [comment removed for export] *)
          pose proof (aapp_disjoint_sh Ab (to_Z n) Ab (to_Z n) R7 ltac:(slia) ltac:(clear - R5 ACEILB; unfold AAPP_HI; slia) R3) as Hbs.
          assert (NE01 : forall x : int, x = t -> x = (t + 1)%uint63 -> False).
          { intros x -> E. apply (f_equal to_Z) in E. rewrite Et1 in E. slia. }
          destruct (Z.eq_dec (to_Z t1) (to_Z t)) as [E1t|E1t].
          * apply to_Z_inj in E1t. subst t1.
            destruct (Enew t r1 (or_introl eq_refl) Hi1) as [(_ & A1 & B1)|(E & _)]; [| exfalso; exact (NE01 t eq_refl E)].
            destruct (Z.eq_dec (to_Z t2) (to_Z (t + 1)%uint63)) as [E2s|E2s].
            -- apply to_Z_inj in E2s. subst t2.
               destruct (Enew (t + 1)%uint63 r2 (or_intror eq_refl) Hi2) as [(E & _)|(_ & A2 & B2)]; [exfalso; symmetry in E; exact (NE01 t eq_refl E)|].
               clear - A1 B1 A2 B2 Hbs. slia.
            -- assert (Hne2 : t2 <> t) by (intros E; apply Hne; rewrite E; reflexivity).
               assert (Hne2s : t2 <> (t + 1)%uint63) by (intros E; apply E2s; rewrite E; reflexivity).
               destruct (Hold t2 r2 Hne2 Hne2s Hi2) as (rg & Hrg2 & El & En). rewrite <- El, <- En.
               destruct (Hnewsep t2 rg Hrg2) as [[D|D] _]; [left | right]; clear - D A1 B1; slia.
          * assert (Hne1t : t1 <> t) by (intros E; apply E1t; rewrite E; reflexivity).
            destruct (Z.eq_dec (to_Z t1) (to_Z (t + 1)%uint63)) as [E1s|E1s].
            -- apply to_Z_inj in E1s. subst t1.
               destruct (Enew (t + 1)%uint63 r1 (or_intror eq_refl) Hi1) as [(E & _)|(_ & A2 & B2)]; [exfalso; symmetry in E; exact (NE01 t eq_refl E)|].
               destruct (Z.eq_dec (to_Z t2) (to_Z t)) as [E2t|E2t].
               ++ apply to_Z_inj in E2t. subst t2.
                  destruct (Enew t r2 (or_introl eq_refl) Hi2) as [(_ & A1 & B1)|(E & _)]; [| exfalso; exact (NE01 t eq_refl E)].
                  clear - A1 B1 A2 B2 Hbs. slia.
               ++ assert (Hne2 : t2 <> t) by (intros E; apply E2t; rewrite E; reflexivity).
                  assert (Hne2s : t2 <> (t + 1)%uint63) by (intros E; apply Hne; rewrite E; reflexivity).
                  destruct (Hold t2 r2 Hne2 Hne2s Hi2) as (rg & Hrg2 & El & En). rewrite <- El, <- En.
                  destruct (Hnewsep t2 rg Hrg2) as [_ [D|D]]; [left | right]; clear - D A2 B2; slia.
            -- assert (Hne1s : t1 <> (t + 1)%uint63) by (intros E; apply E1s; rewrite E; reflexivity).
               destruct (Hold t1 r1 Hne1t Hne1s Hi1) as (q1 & Hq1 & El1 & En1). rewrite <- El1, <- En1.
               destruct (Z.eq_dec (to_Z t2) (to_Z t)) as [E2t|E2t].
               ++ apply to_Z_inj in E2t. subst t2.
                  destruct (Enew t r2 (or_introl eq_refl) Hi2) as [(_ & A1 & B1)|(E & _)]; [| exfalso; exact (NE01 t eq_refl E)].
                  destruct (Hnewsep t1 q1 Hq1) as [[D|D] _]; [right | left]; clear - D A1 B1; slia.
               ++ destruct (Z.eq_dec (to_Z t2) (to_Z (t + 1)%uint63)) as [E2s|E2s].
                  ** apply to_Z_inj in E2s. subst t2.
                     destruct (Enew (t + 1)%uint63 r2 (or_intror eq_refl) Hi2) as [(E & _)|(_ & A2 & B2)]; [exfalso; symmetry in E; exact (NE01 t eq_refl E)|].
                     destruct (Hnewsep t1 q1 Hq1) as [_ [D|D]]; [right | left]; clear - D A2 B2; slia.
                  ** assert (Hne2 : t2 <> t) by (intros E; apply E2t; rewrite E; reflexivity).
                     assert (Hne2s : t2 <> (t + 1)%uint63) by (intros E; apply E2s; rewrite E; reflexivity).
                     destruct (Hold t2 r2 Hne2 Hne2s Hi2) as (q2 & Hq2 & El2 & En2). rewrite <- El2, <- En2.
                     exact (proj2 Hmem'' t1 t2 q1 q2 Hne Hq1 Hq2). }
    (* [comment removed for export] *)
    assert (Hrg0M : iget 0%uint63 (f_mem F) = Some rg0).
    { revert Hrg0'.
      destruct (0 =? t + 1)%uint63 eqn:E01; [apply Uint63.eqb_spec in E01; apply (f_equal to_Z) in E01; rewrite Et1 in E01; change (to_Z 0%uint63) with 0 in E01; slia|].
      destruct (0 =? t)%uint63 eqn:Et0; [apply Uint63.eqb_spec in Et0; apply (f_equal to_Z) in Et0; change (to_Z 0%uint63) with 0 in Et0; slia|].
      change ((0 =? 1)%uint63) with false. cbv iota. intros E; exact E. }
    assert (Ht0f : (t =? 0)%uint63 = false).
    { destruct (t =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. change (to_Z 0%uint63) with 0 in E. slia. }
    assert (Hts0f : (t + 1 =? 0)%uint63 = false).
    { destruct (t + 1 =? 0)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. change (to_Z 0%uint63) with 0 in E. slia. }
    assert (Htst : (t =? t + 1)%uint63 = false).
    { destruct (t =? t + 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. slia. }
    assert (Ht1f : (t =? 1)%uint63 = false).
    { destruct (t =? 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. change (to_Z 1%uint63) with 1 in E. slia. }
    assert (Hts1f : (t + 1 =? 1)%uint63 = false).
    { destruct (t + 1 =? 1)%uint63 eqn:E; [|reflexivity]. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E. rewrite Et1 in E. change (to_Z 1%uint63) with 1 in E. slia. }
    pose proof (sh_aapp_range Ab (to_Z n) R7 R3) as (Q1 & Q2 & Q3).
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
    - rewrite Et17. slia.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ Xmp Hmpres').
    - exact Hheap'.
    - (* [comment removed for export] *) eapply (RFS_via_apres H HH); [exact Xrfs | exact Hpres].
    - exact Hac'.
    - (* [comment removed for export] *) destruct Xst0 as (g & G1' & G2' & G3' & AD). exists g. split; [exact G1'|]. split; [exact G2'|]. split; [exact G3'|].
      destruct AD as [ADn SH]. split; [exact ADn|]. eapply (apres_SHAD H); [exact Hpres | exact SH |].
      (* [comment removed for export] *)
      do 6 right. rewrite shadow_of_length by slia. pose proof (SHAD_aligned _ _ _ SH) as [_ G8].
      assert (M1 : sh aceil <= sh g) by (apply sh_mono; slia).
      assert (M2 : sh g + nsh (q_shi Q - g) <= AHI_LO).
      { clear - G1' G2' G8. unfold nsh, sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. slia. }
      slia.
    - (* [comment removed for export] *) eapply (chain_via_apres H HH); [exact Xch | exact Hpres |]. intros fp ra Hin. rewrite Espu. specialize (XCH0 fp ra Hin). slia.
    - exact XCH0.
    - exact Xs0v.
    - exact Xpfo.
    - (* [comment removed for export] *) exists (done ++ [(0%uint63, n, 0%uint63)]). split; [rewrite Ecsq, Ecs, <- app_assoc; reflexivity | slia].
    - exact XAL0.
    - (* [comment removed for export] *) cbn [map g_tag g_size]. rewrite XG. reflexivity.
    - (* [comment removed for export] *) constructor.
      + cbn [g_id g_addr g_size g_tag]. split; [left; reflexivity|]. split; [exact Erho't|]. split; [slia|]. split; [slia|]. split; [rewrite Et17; slia|]. split.
        * exists (blk_region n 4 iempty). rewrite !iget_iset. rewrite Ht0f, Htst, Uint63.eqb_refl. cbv iota.
          split; [reflexivity|]. unfold blk_region. cbn [rg_lo rg_len rg_kind rg_align]. repeat split; try reflexivity. change (to_Z 4%uint63) with 4. slia.
        * intros rg' Hrg'. rewrite !iget_iset in Hrg'. rewrite Hts0f, Uint63.eqb_refl in Hrg'. cbv iota in Hrg'. injection Hrg' as <-.
          split; [reflexivity|]. split; [exact Erho's|]. cbn [g_addr g_size]. exact Had.
      + apply Forall_forall. intros g Hg.
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hsh).
        pose proof (i63_range (g_tag g)).
        assert (Etg1 : to_Z (g_tag g + 1)%uint63 = to_Z (g_tag g) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
        split; [right; exact Hin|]. split; [subst rho'; rewrite rho_ext_old by slia; exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|].
        split; [rewrite Et17; slia|]. split.
        * exists rgg. rewrite !iget_iset.
          destruct (g_tag g =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); change (to_Z 0%uint63) with 0 in *; slia|].
          destruct (g_tag g =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); slia|].
          destruct (g_tag g =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; exfalso; pose proof (f_equal to_Z Et'); slia|].
          destruct (g_tag g =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); change (to_Z 1%uint63) with 1 in *; slia|].
          split; [exact Hgg|]. repeat split; assumption.
        * intros rg' Hrg'. rewrite !iget_iset in Hrg'.
          destruct (g_tag g + 1 =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; exfalso; pose proof (f_equal to_Z E0); rewrite Etg1 in *; change (to_Z 0%uint63) with 0 in *; slia|].
          destruct (g_tag g + 1 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); rewrite Etg1, Et1 in *; slia|].
          destruct (g_tag g + 1 =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; exfalso; pose proof (f_equal to_Z Et'); rewrite Etg1 in *; slia|].
          destruct (g_tag g + 1 =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; exfalso; pose proof (f_equal to_Z E1); rewrite Etg1 in *; change (to_Z 1%uint63) with 1 in *; slia|].
          destruct (Hsh rg' Hrg') as (Erg' & Hrs & Had'). split; [exact Erg'|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia); exact Hrs|].
          eapply (apres_addressable H); [exact Hpres | exact Had' | exact Hin].
    - (* [comment removed for export] *) cbn [map g_id]. constructor; [|exact XGnd]. intros Hin. apply Hpfresh.
      apply in_map_iff in Hin as (g & <- & Hg). exact (HGids g Hg).
    - (* [comment removed for export] *) cbn [map g_tag]. constructor; [|exact XGtnd]. intros Hin.
      apply in_map_iff in Hin as (g & E & Hg). pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2 & _).
      rewrite E in Htg2. slia.
    - (* [comment removed for export] *) constructor.
      + right. cbn [g_addr g_size g_id g_tag]. split; [| split; [| clear - Xn0; cbn [q_n0] in *; slia]].
        * intros a Hcl Hna. assert (Ha64 : 0 <= a < 2 ^ 64 \/ ~ (0 <= a < 2 ^ 64)) by slia.
          destruct Ha64 as [Ha64|Ha64].
          -- split; [intros Hin; destruct (Hfresh a 1 (Hclient a Ha64 Hcl Hna) ltac:(slia)); slia
                   | intros Hin; destruct (HfreshS a 1 (Hclient a Ha64 Hcl Hna) ltac:(slia)); slia].
          -- pose proof (sh_above_image Ab ltac:(slia)) as SAI. split; intros Hin; clear - Ha64 Hin R1 R5 Q2 Q3 SAI ACEILB; unfold AIMG_TOP, AHI_LO in *; slia.
        * intros b Hb Hni E. apply Hpfresh. rewrite E. apply in_map. exact (XLB0 b Hb Hni).
      + exact XGnew.
    - (* [comment removed for export] *) constructor.
      + cbn [g_addr g_size]. pose proof (stk_of_rw_cells asegs m' Ab _ Hblk) as Hs. cbn [cells_size csize] in Hs.
        rewrite Nat.add_0_r, Z2Nat.id in Hs by slia. exact Hs.
      + apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) XGstk g Hg) as Hs.
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & _ & Hsz & _).
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (G1 & G2 & G3 & G4 & G5 & _).
        apply (stk_pres asegs (ms_mem ms)); [exact Hs|]. intros a Ha. apply Hpres; [slia|].
        unfold aclient_addr. do 2 right. left. exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact Hin | cbn [blk_addr blk_size fst snd]; slia].
    - (* [comment removed for export] *) exact XFF.
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (Hf0 & Hf1 & Hf2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      pose proof (i63_range (f_tag f)).
      assert (Etg1 : to_Z (f_tag f + 1)%uint63 = to_Z (f_tag f) + 1) by (rewrite to_Z_add_small; change (to_Z 1%uint63) with 1; slia).
      assert (Etg2 : to_Z (f_tag f + 2)%uint63 = to_Z (f_tag f) + 2) by (rewrite to_Z_add_small; change (to_Z 2%uint63) with 2; slia).
      split; [subst rho'; rewrite rho_ext_old by slia; exact Hf0|]. split; [subst rho'; rewrite rho_ext_old by (rewrite Etg1; slia); exact Hf1|].
      split; [subst rho'; rewrite rho_ext_old by (rewrite Etg2; slia); exact Hf2|]. split; [exact Hk|]. split; [exact Htg1|]. split; [rewrite Et17; slia|].
      assert (NT : forall x, to_Z x = to_Z (f_tag f) \/ to_Z x = to_Z (f_tag f) + 1 \/ to_Z x = to_Z (f_tag f) + 2 ->
                   (x =? 0)%uint63 = false /\ (x =? t + 1)%uint63 = false /\ (x =? t)%uint63 = false /\ (x =? 1)%uint63 = false).
      { intros x Hx. repeat split;
          (destruct (Uint63.eqb x _) eqn:E; [|reflexivity]; apply Uint63.eqb_spec in E; apply (f_equal to_Z) in E; rewrite ?Et1 in E;
           change (to_Z 0%uint63) with 0 in E; change (to_Z 1%uint63) with 1 in E; exfalso; slia). }
      destruct (NT (f_tag f) ltac:(left; reflexivity)) as (N0 & N1 & N2 & N3).
      destruct (NT (f_tag f + 1)%uint63 ltac:(right; left; exact Etg1)) as (M0 & M1' & M2' & M3).
      destruct (NT (f_tag f + 2)%uint63 ltac:(right; right; exact Etg2)) as (P0 & P1 & P2 & P3).
      split; [exists rgf; rewrite !iget_iset, N0, N1, N2, N3; split; [exact Hgf|]; repeat split; assumption|].
      split; [exists rgs; rewrite !iget_iset, M0, M1', M2', M3; split; [exact Hgs|]; repeat split; assumption|].
      split; [rewrite !iget_iset, P0, P1, P2, P3; exact Hflg|].
      repeat split; assumption.
    - exact XFFnd.
    - exact XFFtnd.
    - (* [comment removed for export] *) destruct XTsep as (S1 & S2 & S3). split; [|split; [|exact S3]].
      + intros g g' [<-|Hg] [<-|Hg'] Hne; cbn [g_tag].
        * exfalso. apply Hne. reflexivity.
        * pose proof (proj1 (Forall_forall _ _) XGin g' Hg') as (_ & _ & _ & _ & Htg2' & _). right. slia.
        * pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & Htg2' & _). left. slia.
        * exact (S1 g g' Hg Hg' Hne).
      + intros g f [<-|Hg] Hf; cbn [g_tag].
        * pose proof (proj1 (Forall_forall _ _) XFFin f Hf) as (_ & _ & _ & _ & _ & Hftg2 & _). right. slia.
        * exact (S2 g f Hg Hf).
    - exact XFFlen.
    - exact XXS.
    - (* [comment removed for export] *) intros t' rg' Ht'. rewrite !iget_iset in Ht'.
      destruct (t' =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; left; exact E0|].
      destruct (t' =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; do 5 right; left; cbn [map g_tag]; left; symmetry; exact Ets|].
      destruct (t' =? t)%uint63 eqn:Et'; [apply Uint63.eqb_spec in Et'; do 4 right; left; cbn [map g_tag]; left; symmetry; exact Et'|].
      destruct (t' =? 1)%uint63 eqn:E1; [apply Uint63.eqb_spec in E1; right; left; exact E1|].
      destruct (Xdom t' rg' Ht') as [H0' | [H1' | [H2' | [H3' | [Hb' | [Hbs' | Hf']]]]]];
        [left; exact H0' | right; left; exact H1' | do 2 right; left; exact H2' | do 3 right; left; exact H3'
        | do 4 right; left; cbn [map]; right; exact Hb' | do 5 right; left; cbn [map]; right; exact Hbs' | do 6 right; exact Hf'].
    - (* [comment removed for export] *) destruct Xreg0 as (rg0_ & Hrg0_ & Hlo0 & Hlen0 & Hd0 & Hpg0).
      assert (Erg0 : rg0 = rg0_) by (fold F in Hrg0_; congruence). subst rg0_.
      exists (err_region K (t + 16) rg0 pe). rewrite iget_iset_same. split; [reflexivity|].
      unfold err_region. cbn [rg_lo rg_len rg_dflt rg_pages]. split; [exact Hlo0|]. split; [exact Hlen0|]. split; [exact Hd0|].
      intros pn p' Hp'. rewrite iget_iset in Hp'. destruct (pn =? c_errcell K >> 12)%uint63 eqn:Epn.
      + apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_kind]. exact (Hpg0 _ _ Hpe).
      + exact (Hpg0 _ _ Hp').
    - (* [comment removed for export] *) destruct Xreg1 as (rg1_ & Hrg1_ & Hlo1 & Hlen1 & Hd1 & Hk1' & Hal1). fold F in Hrg1_. rewrite Hrg1 in Hrg1_. injection Hrg1_ as <-.
      exists (drop_below off rg1). rewrite !iget_iset. change ((1 =? 0)%uint63) with false.
      destruct (1 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); rewrite Et1 in *; change (to_Z 1%uint63) with 1 in *; slia|].
      destruct (1 =? t)%uint63 eqn:Et1'; [apply Uint63.eqb_spec in Et1'; exfalso; pose proof (f_equal to_Z Et1'); change (to_Z 1%uint63) with 1 in *; slia|].
      change ((1 =? 1)%uint63) with true. cbv iota. split; [reflexivity|]. unfold drop_below. cbn [rg_lo rg_len rg_dflt rg_kind rg_align]. repeat split; assumption.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((2 =? 0)%uint63) with false.
      destruct (2 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); rewrite Et1 in *; change (to_Z 2%uint63) with 2 in *; slia|].
      destruct (2 =? t)%uint63 eqn:Et2'; [apply Uint63.eqb_spec in Et2'; exfalso; pose proof (f_equal to_Z Et2'); change (to_Z 2%uint63) with 2 in *; slia|].
      change ((2 =? 1)%uint63) with false. exact Xreg2.
    - (* [comment removed for export] *) rewrite !iget_iset. change ((3 =? 0)%uint63) with false.
      destruct (3 =? t + 1)%uint63 eqn:Ets; [apply Uint63.eqb_spec in Ets; exfalso; pose proof (f_equal to_Z Ets); rewrite Et1 in *; change (to_Z 3%uint63) with 3 in *; slia|].
      destruct (3 =? t)%uint63 eqn:Et3'; [apply Uint63.eqb_spec in Et3'; exfalso; pose proof (f_equal to_Z Et3'); change (to_Z 3%uint63) with 3 in *; slia|].
      change ((3 =? 1)%uint63) with false. exact Xreg3.
    - (* [comment removed for export] *) destruct Xro as (rg0_ & Hrg0_ & Hroc).
      assert (rg0_ = rg0) by (fold F in Hrg0_; congruence). subst rg0_.
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
             rewrite Z.mod_small in Hir by slia.
             split; [Z.div_mod_to_equations; nia | split; [Z.div_mod_to_equations; nia | intros v Ev; injection Hc as Ec; rewrite Ev in Ec; unfold err_cell in Ec; discriminate Ec]].
          -- exact (Xinb 0%uint63 rg0 _ pe ci c Hrg0M Hpe Hc).
        * exact (Xinb 0%uint63 rg0 pn p' ci c Hrg0M Hp' Hc).
      + destruct (t' =? t + 1)%uint63 eqn:Ets.
        * (* [comment removed for export] *)
          injection Ht' as <-. unfold sh_region in Hp' |- *. cbn [rg_pages rg_len] in Hp' |- *. rewrite iget_iset, iget_iempty in Hp'.
          destruct (pn =? 0)%uint63 eqn:Epn; [|discriminate]. apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-. cbn [pg_cells] in Hc.
          pose proof (i63_range ci). destruct (sh_cells_inv n ci c ltac:(slia) Hc) as [Hcilt ->].
          rewrite (nsh_eq n) by slia. change (to_Z 0%uint63) with 0.
          split; [Z.div_mod_to_equations; slia|]. split; [Z.div_mod_to_equations; slia|].
          intros v Ev. unfold sh_cell in Ev. destruct (((ci + 1) * 8 <=? n >> 3))%uint63 eqn:Ecv; [|discriminate].
          apply (proj1 (leb8_spec ci n ltac:(slia) ltac:(slia))) in Ecv. Z.div_mod_to_equations. slia.
        * destruct (t' =? t)%uint63 eqn:Et'.
          -- injection Ht' as <-. unfold blk_region in Hp'. cbn [rg_pages] in Hp'. rewrite iget_iempty in Hp'. discriminate.
          -- destruct (t' =? 1)%uint63 eqn:E1.
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
        * destruct (t' =? 1)%uint63 eqn:E1.
          -- injection Ht' as <-. apply Uint63.eqb_spec in E1. subst t'. fold F in Hrg1. destruct (Xkinds 1%uint63 rg1 Hrg1 Ht'0) as [Hdu1 Hku1].
             unfold drop_below. cbn [rg_dflt rg_pages]. split; [exact Hdu1|].
             intros pn p' Hp'. destruct (drop_below_pages_inv _ _ _ _ Hp') as (p0 & Hp0 & _ & ->).
             unfold drop_page. cbn [fst snd]. destruct (pn =? off >> 12)%uint63; cbn [pg_kind]; exact (Hku1 _ _ Hp0).
          -- exact (Xkinds t' rg' Ht' Ht'0).
    - (* [comment removed for export] *) cbn [lb_bytes fold_right blk_size snd]. fold (lb_bytes LB). rewrite Ecost. slia.
    - (* [comment removed for export] *) cbn [length]. rewrite Ecnt. slia.
    - (* [comment removed for export] *) apply (stk_merge asegs m' (q_lo Q) (bv_unsigned (rv rho F 2)) (q_sp0 Q)); [exact Hstk' | | rewrite Espu; slia].
      apply (stk_pres asegs (ms_mem ms)); [exact Hstk_hi|]. intros a Ha. apply Hpres; [|left; slia].
      destruct Hstk_hi as (_ & Hhi64 & _). rewrite Espu in Ha. slia.
    - repeat split; assumption.
    - exact Haux'.
    - exact Hinv'.
    - rewrite EerrA in Herr'. pose proof (stk_of_rw_cells asegs m' (errA A) [C4 errv'] Herr') as Hs. cbn [cells_size csize] in Hs.
      replace (errA A + Z.of_nat 4) with (errA A + 4) in Hs by slia. exact Hs.
    - (* [comment removed for export] *) exact (HSH0 _ Hac' Hinv').
    - intros b Hb Hni. right. exact (XLB0 b Hb Hni).
    - exact XLB0h.
    - split; [exact XG0in | exact XLB0nd].
    - (* [comment removed for export] *) intros b [<- | Hb].
      + right. exists (GB t p Ab n). split; [left; reflexivity | reflexivity].
      + destruct (XLBsub b Hb) as [Hb0 | (g & Hg & ->)]; [left; exact Hb0 | right; exists g; split; [right; exact Hg | reflexivity]].
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (Xframe a Ha Hcl Hna Hnx Hne Hnxs).
      apply Hpres; [exact Ha | exact (Hclient_addr a Ha Hcl Hna)].
    - (* [comment removed for export] *) apply Forall_forall. intros f__ Hf__. pose proof (proj1 (Forall_forall _ _) XFFstk f__ Hf__) as HsF.
      destruct (aframe_of_FF H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hf__) as [(KF1 & KF2 & KF3 & KF4 & KF5) (FB1 & FB2 & FB3 & FB4)].
      apply (stk_pres asegs (ms_mem ms)); [exact HsF|]. intros a__ Ha__.
      apply Hpres; [clear - Ha__ KF2 KF3 FB1 FB2; acb; unfold AFS_HDR, AIMG_TOP in *; slia| unfold aclient_addr; do 4 right; left; clear - Ha__ KF2 KF3; unfold AFS_HDR in *; slia].
  Qed.
End NodeM.
