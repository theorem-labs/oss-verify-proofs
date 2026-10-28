(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnDivWords BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib BgArith BgMont BgExp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require W_ctx3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ExpKitArr ValArr W_mod_exp W_exp_simple W_mont PlaceMont W_mont_ctx W_exp_mont W_gueron_arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac the_mi := lazymatch goal with H : mem_inv bgusegs _ |- _ => exact H end.
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma kenv_read_ro : forall (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z)
    (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem),
  alloc_ceiling <= lo -> lo <= FB -> FB <= SPv -> frames_ok PL SPv B ->
  forall fr st bs m OW n an,
  kenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL n an -> n <> ROne ->
  exists Dn, rw_cells bgusegs m an (bn_cells Dn (getbn n bs)) /\ u64arr bgusegs m Dn (wlimbs (bn_buf (getbn n bs))) /\ bg_ok (getbn n bs)
    /\ 0 <= Dn
    /\ (forall r a, ref_at bs OW PL r a -> a + 24 <= Dn \/ Dn + 8 * Z.of_nat (bn_dmax (getbn n bs)) <= a)
    /\ (forall r p D, r <> n -> vref r bs -> bn_d (getbn r bs) = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax (getbn r bs))) OW ->
          D + 8 * Z.of_nat (bn_dmax (getbn r bs)) <= Dn \/ Dn + 8 * Z.of_nat (bn_dmax (getbn n bs)) <= D)
    /\ ((0 < bn_dmax (getbn n bs))%nat -> 0 < Dn /\ Dn mod 8 = 0).
Proof.
  intros LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL FBlo FBsp FROK fr st bs m OW n an ENV LS HA NRO.
  pose proof ENV as (HEAP & _). pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
  destruct (lib_state_open [] bs m OW PL EA n an LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
  destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK n D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
  exists D. split; [exact BN|]. split; [exact U|]. split; [exact OK|]. split; [exact D0|]. split; [exact SEP|].
  split; [|intros HD0; exact (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR HD0)].
  intros r p Dr NE HVr Edr Hinr.
  pose proof (RH_range _ _ _ _ _ _ _ HEAP Hinr) as (B0 & _ & _ & BC & _).
  destruct (bn_d (getbn n bs)) as [pn|] eqn:Ed.
  - unfold bn_arr in ARR. rewrite Ed in ARR. destruct ARR as [Hin _].
    exact (limbs_limbs_disj st OW LB m HEAP bs PL EA PARTS r n p Dr _ pn D _ NE HVr HV Edr Ed Hinr Hin).
  - destruct DC as [DC|[DC _]]; [|left; clear - BC DC CEIL FBlo FBsp; lia].
    unfold bn_arr in ARR. rewrite Ed in ARR.
    destruct (pl_of PL n) as [[x q off|x|x d|x]|] eqn:Ep.
    + destruct ARR as [-> Eb]. right. unfold bn_dmax. rewrite Eb. cbn [length]. clear - B0. lia.
    + destruct ARR as [-> Eb]. right. unfold bn_dmax. rewrite Eb. cbn [length]. clear - B0. lia.
    + exfalso. destruct ARR as (-> & _ & HL).
      destruct (pl_of_cases PL n _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NRO eq_refl)| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists n. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
      destruct (frame_iv_range _ _ _ _ _ _ PARTS FROK _ HFd) as (Cd & Sd & Ud). cbn [fst snd] in Cd, Sd, Ud.
      unfold bn_dmax in DC. rewrite HL in DC. clear - DC Cd. lia.
    + exfalso. destruct (pl_of_cases PL n _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NRO eq_refl)| discriminate E'|].
      pose proof (proj1 (proj1 (proj2 PARTS)) n _ Eb) as (_ & _ & _ & Fx). exact Fx.
    + destruct ARR as [-> Eb]. right. unfold bn_dmax. rewrite Eb. cbn [length]. clear - B0. lia.
Qed.

Section Proofs.
  Variable CS : Z.
  Hypothesis CS96 : 128 <= CS.
  Hypothesis CSwexp : W_expand.BN_WEXPAND_STACK <= CS.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma gueron_fill_all : GFILL_all CS.
  Proof.
    unfold GFILL_all. intros ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL0 EA arr arp ac qc am qm FB SPv jz jv rm arm
      ESPV CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK LOF HPC HFM AMR HAm NROm.
    unfold GFILL_stmt. intros until t6; intros ENVT LST VTT HAqT Er HAmT NEQ TOP1 TB.
    set (PL := pl_set_mont PL0 (Some (am, qm))) in *.
    pose proof (kenv_pre LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B SPv FB CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (kenv_read LB PL EA lo B SPv FB s bs OW m CEIL FROK) as KREAD.
    pose proof (kenv_read_ro LB PL EA lo B SPv FB s bs OW m CEIL FBlo FBsp FROK) as KRO.
    pose proof (kenv_hole1 LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KHOLE1.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - FBlo FBsp SPR2 CEIL; lia).
    pose proof GLO' as GLO2; unfold GLOBALS_TOP in GLO2.
    assert (LOFW : lo <= FB - W_expand.BN_WEXPAND_STACK) by (clear - LOF CSwexp; lia).
    assert (NROq : rq <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; lia).

    destruct (KRO _ _ _ _ _ rm arm ENVT LST HAmT NROm) as (Dm0 & _ & _ & (OKm1 & OKm2 & OKm3 & OKm4) & _ & _ & _ & _).
    set (bmT := getbn rm bsT) in *. set (j := bn_top bmT) in *.
    assert (J512 : Z.of_nat j <= 512) by (unfold BG_DMAX in OKm3; clear - OKm2 OKm3; lia).
    clear Dm0 OKm1 OKm4.
    unfold implM. iprefix.

    step. step. step.
    destruct (KPRE _ _ _ _ _ W_expand.BN_WEXPAND_STACK ENVT LST LOFW) as (errv1 & PRE1).
    ihere. to_implM.
    eapply implM_embed_bind.
    { eapply (W_expand.bn_wexpand_walk HM HF); [exact PRE1| reflexivity| exact HAqT| rewrite Er; apply wref_pool| reflexivity| reflexivity| clear - J512; lia]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & -> & HDM1 & WXR1 & BST1)).
    destruct (KPOST _ _ _ _ _ _ _ _ _ ENVT KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
    cbn [fst snd] in *. clear PRE1 KP.
    replace (ret_pc (Z_to_bv 64 0x15049c)) with (Z_to_bv 64 0x15049c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAqT) as HAq2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAmT) as HAm2.
    assert (EM1 : getbn rm bs1 = bmT).
    { destruct WXR1 as [[_ ->]|[_ (pn & ->)]]; [reflexivity| apply getbn_setbn_other; exact NEQ]. }
    set (rb := getbn rq bs1) in *.
    assert (HDr : (0 < bn_dmax rb)%nat) by (clear - HDM1 TOP1; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAq2) as HVq2.
    destruct (KREAD _ _ _ _ _ rq ar ENV2 LS2 HAq2 ltac:(rewrite Er; apply wref_pool) HDr)
      as (Dr & pr & Edr & Hinr & BNr & Ur & (OKr1 & OKr2 & OKr3 & OKr4) & (Ar0 & ArS & Ar63 & ArI) & (Dr0 & DrS & DrI) & SEPr & _).
    destruct (KRO _ _ _ _ _ rm arm ENV2 LS2 HAm2 NROm) as (Dm & BNm & Um & (OKm1 & _ & _ & _) & Dm0 & SEPm & LLm & ALm).
    rewrite EM1 in BNm, Um, OKm1, SEPm, LLm, ALm.
    fold rb in Edr, Hinr, BNr, Ur, OKr1, OKr2, OKr3, OKr4, DrS, DrI, SEPr.
    pose proof (LLm rq pr Dr NEQ HVq2 Edr Hinr) as DJ. fold rb in DJ.
    pose proof (SEPm rq ar HAq2) as SQM. pose proof (SEPr rq ar HAq2) as SQR.
    clear SEPr SEPm LLm.
    destruct (KHOLE1 _ _ _ _ _ rq ar Dr pr 0 ENV2 LS2 HAq2 NROq Edr Hinr ltac:(clear; lia) ltac:(clear - FBlo; lia)) as (FRAMEH & CLOSE).
    fold rb in FRAMEH, CLOSE.
    pose proof ENV2 as (_ & _ & ST & (errv2 & ERR) & MI & _ & _ & _ & _ & FR & _).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_cells in BNr, BNm. unfold BG_DMAX in OKr3, OKm3.
    pose proof (munch_refl (fpw1 FB 0 ar Dr (bn_dmax rb)) m2) as MU. pose proof (wmono_refl bgusegs m2) as WM.
    unfold fpw1 in MU.
    assert (ArR : 0 < ar < 2^64) by (clear - Ar0 Ar63; lia).

    unfold bset. cbn [tree_ops]. rewrite EM1. fold rb. fold j.
    unfold implM. iprefix.
    unfold MallocRep.wz.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - ArR; lia); zify_cond KZ; [exfalso; clear - KZ ArR; lia| clear KZ].
    step.
    unfold MallocRep.wz.
    assert (LBm : length (bn_buf bmT) = bn_dmax bmT) by reflexivity.
    assert (LBr : length (bn_buf rb) = bn_dmax rb) by reflexivity.
    assert (J1 : (1 <= j)%nat) by exact TOP1.
    destruct (ALm ltac:(clear - OKm2 J1; lia)) as (DmP & DM8). clear ALm.
    assert (DmR : Dm < 2^64) by (pose proof (u64arr_bound _ _ _ _ Um) as X; rewrite wlimbs_len, LBm in X; clear - X OKm2 J1; lia).
    destruct (ref_at_ualign _ _ _ _ _ _ _ _ _ (proj1 ENV2) (lib_state_h_parts _ _ _ _ _ _ LS2) HAq2 NROq) as (_ & AR8).
    destruct (block_ualign _ _ _ _ _ _ _ (proj1 ENV2) Hinr) as (_ & DR8).
    assert (DrR : Dr < 2^64) by (clear - Dr0 DrS FBlo FBsp SPR2; lia).
    ub_chk. zstep. ub_chk.
    ub_chk. zstep. ub_chk.
    step.
    ub_chk. zstep. ub_chk.
    assert (NTH0 : nth_error (wlimbs (bn_buf bmT)) (Z.to_nat 0) = Some (Z_to_bv 64 (nth 0 (bn_buf bmT) 0))).
    { apply nth_error_wlimbs. clear - OKm2 J1 LBm. lia. }
    let a := cur_mem_addr in pose proof (u64arr_read bgusegs m2 Dm _ 0 _ a Um NTH0 ltac:(lia) ltac:(addr_tac)) as RD.
    step. clear RD NTH0 BNm.

    assert (FRD : disjoint_from [(FB - 0, FB); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax rb))] FB 400).
    { cbn [disjoint_from]. split; [right; clear; lia|]. split; [clear - ArS ESPV FBlo; lia|]. split; [right; clear - DrS FBlo; lia| exact I]. }
    assert (ERD : disjoint_from [(FB - 0, FB); (ar, ar + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax rb))] 3346164 4).
    { cbn [disjoint_from]. split; [left; clear - FBlo GLO2; lia|]. split; [clear - ArI; lia|]. split; [clear - DrI; lia| exact I]. }
    apply hide_intro in FR. apply hide_intro in ERR.

    eapply evt_cut.
    { eapply gueron_fill_walk with (lo := lo) (RD := Dr) (MD := Dm) (R := bn_buf rb) (M := bn_buf bmT) (j := j);
        [exact OKm1| exact J1| rewrite LBr; exact HDM1| rewrite LBm; exact OKm2| clear - J512; lia| rewrite LBm, LBr; clear - DJ; lia
        | exact Ur| exact Um| exact MI| rewrite ESP; exact ST]. }
    clear Ur Um ST MI.
    intros ms' PO. unfold gf_post in PO.
    destruct PO as (y12 & y13 & y14 & y15 & y16 & y17 & m3 & E & MUc & WMc & MIc & Ur3 & Um3 & STc). subst ms'.
    rewrite ESP in STc. clear Um3.
    transport_after_call bgusegs m2 m3 MUc WMc. clear MUc WMc.

    assert (LG : length (gfin (bn_buf rb) (bn_buf bmT) j) = length (bn_buf rb)) by (apply gfin_length; [rewrite LBr; exact HDM1| rewrite LBm; exact OKm2]).
    assert (LUr : Z.of_nat (length (wlimbs (gfin (bn_buf rb) (bn_buf bmT) j))) = Z.of_nat (bn_dmax rb)) by (rewrite wlimbs_len, LG, LBr; reflexivity).
    apply hide_intro in OKr4. apply hide_intro in DJ. apply hide_intro in SQM. apply hide_intro in ArI. apply hide_intro in DrI.
    apply hide_intro in ArS.
    pose proof FR as FRl. apply hide_elim in FRl.
    eapply (rw_cells_transport bgusegs _ m2 m3) in FRl; [| exact MU | exact WM | exact FRD].
    unfold efrM, efrMv in FRl.
    replace (Z_to_bv 64 SPv) with (Z_to_bv 64 (FB + 400)) by (f_equal; clear - ESPV; lia).
    step.
    replace (Z_to_bv 64 (FB + 400)) with (Z_to_bv 64 SPv) by (f_equal; clear - ESPV; lia).
    clear FRl.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    apply hide_elim in FR. apply hide_elim in ERR.
    eapply (rw_cells_transport bgusegs _ m2 m4) in FR; [| exact MU | exact WM | exact FRD].
    eapply (rw_cells_transport bgusegs _ m2 m4) in ERR; [| exact MU | exact WM | exact ERD].

    set (b2 := mkBN (bn_d rb) (gfin (bn_buf rb) (bn_buf bmT) j) j (bn_neg rb) (bn_flags rb)) in *.
    apply hide_elim in OKr4.
    assert (OK2 : bg_ok b2).
    { unfold bg_ok, BG_DMAX. change (bn_dmax b2) with (length (gfin (bn_buf rb) (bn_buf bmT) j)). cbn [b2 bn_buf bn_top bn_flags]. rewrite LG, LBr.
      split; [apply gfin_limbs; [exact OKr1| exact OKm1]|]. split; [exact HDM1|]. split; [exact OKr3| exact OKr4]. }
    destruct (CLOSE m4 b2 errv2 MU WM) as (ENV3 & LS3).
    { change (bn_cells Dr b2) with [C8 (wz Dr); C4 (wz (Z.of_nat j)); C4 (wz (Z.of_nat (length (gfin (bn_buf rb) (bn_buf bmT) j))));
                                    C4 (wz (Z.b2z (bn_neg rb))); C4 (wz (bn_flags rb))].
      rewrite LG, LBr. exact BNr. }
    { exact Ur3. } { reflexivity. } { exact LG. } { exact OK2. } { exact STc. } { exact MIc. } { exact FR. }
    { unfold LX_ERRNO, RATP. exact ERR. }
    ihere. cbn [embed interp]. apply implM_interp_ret. apply evt_done.
    unfold LOOPQ. exists m4, OW2. do 15 eexists. split; [reflexivity|]. cbn [snd].
    split; [exact ENV3|]. split; [exact LS3|].
    split; [| apply ref_at_setbn; exact HAq2].
    eapply (vtab_stable PL0 am qm bsT OWT); [exact VTT|]. eapply refs_stable_trans; [exact RS2| apply refs_stable_setbn].
  Qed.

  Definition BN_mod_exp_mont_walk CSnew CSfree Wstart Wget Wend Wmul Wto Wfrom Wset Wucmp Wnnmod Wsetw
    : exp_stmt_f BN_MOD_EXP_MONT (BN_MOD_EXP_MONT_STACK CS) (BN_mod_exp_mont (tree_ops bptr)) (Some (wz 0)) :=
    BN_mod_exp_mont_walk_gf CS CS96 CSnew CSfree HM HF Wstart Wget Wend Wmul Wto Wfrom Wset Wucmp Wnnmod Wsetw gueron_fill_all.
End Proofs.
End WithCeiling0.
