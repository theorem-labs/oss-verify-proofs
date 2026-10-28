(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BgState BgInv BgLib BgArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_expand W_ctx BnCall BnRKit W_ctx_end W_div_tail W_div.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ops := (tree_ops bptr).

Definition octop (o : option bnref) (bs : bstate bptr) : bstate bptr :=
  match o with Some r => setbn r (bn_correct_top_pure (getbn r bs)) bs | None => bs end.

Lemma div_fin_eq : forall (dv rm : option bnref) (bs : bstate bptr),
  bbind ops (match dv with Some r => bbind ops (bget ops r) (fun b => bset ops r (bn_correct_top_pure b)) | None => bret ops tt end)
    (fun _ => match rm with Some r => bbind ops (bget ops r) (fun b => bset ops r (bn_correct_top_pure b)) | None => bret ops tt end) bs
  = TRet (tt, octop rm (octop dv bs)).
Proof. intros [d|] [r|] bs; reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_DIV : Z := 0x10966c.
Definition BN_DIV_TOP_STACK : Z := 64 + BN_DIV_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma ctop_call : forall (POST : machine_state -> Prop) (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z)
      (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem) (fr : list cell)
      (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= FB - 16 -> FB <= SPv -> SPv <= B -> SPv < 2^64 -> frames_ok PL SPv B ->
    cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> wref PL r ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        cenv LB PL lo B SPv FB s0 bs0 OW0 m0 fr st (setbn r (bn_correct_top_pure (getbn r bs)) bs) m' OW ->
        lib_state (setbn r (bn_correct_top_pure (getbn r bs)) bs) m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_CORRECT_TOP) fc None m (seg_rom bgusegs)).
  Proof.
    intros until fc. intros CEIL GLO' LO16 FBSP SPB SPR FROK ENV LS HA WR K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (proj1 WR) as NRO.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    set (b := getbn r bs) in *.
    assert (ESPv : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - CEIL LO16 FBSP SPR; lia).
    assert (LOFB : lo <= FB) by (clear - LO16; lia).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold BG_DMAX in OK3. pose proof GLO' as GLO. unfold GLOBALS_TOP in GLO.
    assert (UBD : ub_ptr_ok (Z.of_nat (bn_top b)) D).
    { unfold ub_ptr_ok. intros HT. eapply bn_arr_ualign; [exact HEAP | exact PARTS | exact ARR | clear - HT OK2; unfold bn_dmax in *; lia]. }
    eapply evt_cut.
    { eapply bn_correct_top_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HA NRO) | exact UBD | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESPv; exact ST | rewrite ESPv; clear - LO16; lia | exact MI
        | rewrite ESPv; clear - AC CEIL LO16 FBSP; lia | rewrite ESPv; clear - DC CEIL LO16 FBSP; lia | exact SEPr | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESPv in *.
    assert (U' : u64arr bgusegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - DC CEIL LO16 FBSP; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgusegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite FSZ; split; [right; clear; lia|]; split; [clear - AC CEIL LOFB FBSP; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - GLO LO16; lia|]; split; [clear - AI A0; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; clear - CEIL LO16 FBSP; lia|].
      constructor; [eapply (w_struct OW LB bs PL EA SPv false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; clear - LO16 FBSP; lia|]. constructor; [right; right; exists r, ar; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| clear; lia] | constructor]. }
    assert (LS' : lib_state (setbn r (bn_correct_top_pure b) bs) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame st LB SPv B [r] bs m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_correct_top_pure, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - destruct (strip_top_spec (bn_buf b) (bn_top b) OK2) as (S1 & _ & _).
        unfold bg_ok, bn_correct_top_pure, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [clear - S1 OK2; lia|]. split; [clear - OK3; lia| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbn.
    eapply (cenv_silent LB PL EA lo B SPv FB s0 bs0 OW0 m0 CEIL GLO' LOFB FBSP SPB FROK fr fr st bs m m' OW _ errv);
      [exact ENV | exact LS | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ].
  Qed.

  Lemma BN_div_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (dv rm : option bnref) (num dvs : bnref) (adv arm anum advs ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_DIV_TOP_STACK -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) ->
    oref_at bs OW PL dv adv -> oref_at bs OW PL rm arm -> ref_at bs OW PL num anum -> ref_at bs OW PL dvs advs ->
    (forall d, dv = Some d -> wref PL d) -> (forall r, rm = Some r -> hpl PL r) -> num <> ROne -> dvs <> ROne ->
    a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz ac ->
    implM bgusegs (interp (embed (BN_div ops dv rm num dvs bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
               (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros PRE -> EC HAdv HArm HAnum HAdvs WRdv HPrm NROn NROd -> -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    unfold BN_DIV_TOP_STACK, BN_DIV_STACK, BN_DIV, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold BN_div. rewrite bbind_get.
    set (bd := getbn dvs bs) in *.

    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAdvs) as HVdvs.
    destruct (lib_state_open [] bs m OW PL EA dvs advs LS ND HAdvs ltac:(intros []) NROd) as ((Dd & BNd & ARRd) & (OKd1 & OKd2 & OKd3 & OKd4) & _).
    fold bd in BNd, ARRd, OKd1, OKd2, OKd3, OKd4.
    destruct (bn_arr_facts s OW LB m HEAP bs PL EA _ _ PARTS FROK dvs Dd HVdvs NROd ARRd) as (Ud & _ & Dd0 & DdC & _ & _).
    fold bd in Ud, DdC.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAdvs NROd) as (DA0 & DAC & _).
    destruct (proj1 (limbarr_limbs_at bgusegs m Dd (bn_buf bd)) Ud) as (LAd & _).
    unfold BG_DMAX in OKd3. unfold bn_cells in BNd. unfold MallocRep.wz in BNd. clear Ud.
    assert (ADVS : 0 < advs /\ advs + 24 < 18446744073709551616) by (clear - DA0 DAC CEIL LO SPR; lia).
    assert (DASEP : advs + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= advs) by (clear - DAC CEIL LO; lia).
    assert (DDSEP : Dd + 8 * Z.of_nat (bn_dmax bd) <= bv_unsigned sp - 80 \/ bv_unsigned sp <= Dd) by (clear - DdC CEIL LO; lia).
    assert (DDR : 0 <= Dd /\ Dd + 8 * Z.of_nat (bn_dmax bd) < 18446744073709551616) by (clear - Dd0 DdC CEIL LO SPR; lia).
    assert (TOPD : Z.of_nat (bn_top bd) <= 512) by (clear - OKd2 OKd3; lia).
    clear DAC OKd4 DA0 Dd0.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    apply hide_intro in NROn. apply hide_intro in NROd.
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 8 step. do 8 zstep.

    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    eapply evt_cut.
    { eapply BN_is_zero_spec with (lo := lo) (A := advs) (D := Dd) (b := bd);
        [exact BNd | exact (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAdvs (hide_elim _ NROd)) | clear - TOPD; lia | rewrite ESP; exact ST | rewrite ESP; clear - LO; lia | exact MI | rewrite ESP; clear - DASEP; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & a0z & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & E & MUc & WMc & MIc & STc & ->).
    subst ms'. rewrite ESP in *.
    replace (ret_pc (Z_to_bv 64 1087148)) with (Z_to_bv 64 1087148) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LAd2 : limbs_at bgusegs m2 Dd (bn_buf bd)).
    { eapply limbs_at_transport; [eapply limbs_at_transport; [exact LAd | exact MU |] | exact MUc |];
        cbn [disjoint_from]; fold (bn_dmax bd); (split; [clear - DDSEP; lia| exact I]). }
    clear ST MI. transport_after_call bgusegs m1 m2 MUc WMc. clear MUc WMc.
    zstep. if_cases KZ; zify_cond KZ.
    2:{
        ihere. to_implM.
        replace (bn_top bd =? 0)%nat with true by (destruct (bn_top bd =? 0)%nat; [reflexivity| exfalso; cbn in KZ; rewrite ?unsigned_lit in KZ by lia; lia]).
        unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
    apply Nat.eqb_neq in KZ.

    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HAdvs (hide_elim _ NROd)) as (DAP & DA8).
    pose proof (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARRd ltac:(unfold bn_dmax in *; clear - KZ OKd2; lia)) as (DDP & DD8).
    assert (RTOP : 0 < Z.of_nat (bn_top bd) < 8388609) by (clear - TOPD KZ; lia).
    repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
    chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; lia).
    zstep. rewrite (land7 advs) by exact DA8.
    chk ltac:(fun C => clear - C; lia).
    step. rewrite (sx32_small (Z.of_nat (bn_top bd))) by (clear - RTOP; lia).
    zstep. rewrite (bk_swrap32_small (Z.of_nat (bn_top bd) + -1)) by (clear - RTOP; lia).
    zstep. rewrite lts_signed by (clear - RTOP; lia). if_cases KO; zify_cond KO. { exfalso. clear - KO. lia. } clear KO.
    step. do 2 zstep.
    replace (Dd + (Z.of_nat (bn_top bd) + -1) ≪ 3) with (Dd + 8 * (Z.of_nat (bn_top bd) - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    set (dtop := nth (bn_top bd - 1) (bn_buf bd) 0) in *.
    assert (Ntop : nth_error (bn_buf bd) (bn_top bd - 1) = Some dtop) by (apply nth_error_nth'; unfold bn_dmax in *; clear - KZ OKd2; lia).
    assert (Rdtop : 0 <= dtop < 18446744073709551616).
    { assert (L : limb dtop) by (apply limbs_nth; exact OKd1). unfold limb in L. rewrite BW_lit in L. clear - L. lia. }
    assert (RDD : Dd + 8 * Z.of_nat (bn_top bd) < 18446744073709551616) by (clear - DDR OKd2; unfold bn_dmax in *; lia).
    do 2 zstep. rewrite ?land64_small by (clear - DDP RDD RTOP CEIL LO SPR; lia).
    replace (0 <? Dd) with true by (symmetry; apply Z.ltb_lt; exact DDP).
    replace (Dd + 8 * (Z.of_nat (bn_top bd) - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; clear - DDP RTOP; lia).
    cbn [Z.b2z].
    chk ltac:(fun C => clear - C; lia).
    do 4 zstep.
    rewrite (lxor_signbit63' (Z.of_nat (bn_top bd) + -1)) by (clear - RTOP; lia).
    replace (Z.of_nat (bn_top bd) + -1 + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; clear - RTOP; lia).
    replace (Dd + 8 * (Z.of_nat (bn_top bd) - 1) <? Dd) with false by (symmetry; apply Z.ltb_ge; clear - RTOP; lia).
    cbn [Z.b2z Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    chk ltac:(fun C => rewrite ?unsigned_lit in C by (clear - DDP RDD CEIL LO SPR; lia); clear - C DDP; lia).
    zstep. rewrite (land7 (Dd + 8 * (Z.of_nat (bn_top bd) - 1))) by (clear - DD8; Z.div_mod_to_equations; lia).
    chk ltac:(fun C => clear - C; lia).
    assert (TOP1 : 1 <= Z.of_nat (bn_top bd)) by (clear - KZ; lia).
    apply hide_intro in KZ.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs m2 Dd (bn_buf bd) (bn_top bd - 1) dtop ad LAd2 Ntop ltac:(unfold wa; f_equal; clear - TOP1; lia)) as RD.
    zstep. clear RD.
    repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
    zstep. if_cases KT; zify_cond KT.
    {
      ihere. to_implM.
      replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact (hide_elim _ KZ)).
      replace (dtop =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in KT by lia; lia).
      unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
    do 6 zstep.

    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m2 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    assert (GLO' : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia).
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr s bs m2 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|].
      split; [exact STc|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MIc|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    pose proof (cenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp SPB SPR2 FROK) as CPRE.
    pose proof (cenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m CEIL GLO' FBlo FBsp FROK) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (CPRE _ _ _ _ _ BN_DIV_STACK ENV LS1 ltac:(unfold BN_DIV_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact (hide_elim _ KZ)).
    replace (dtop =? 0) with false by (symmetry; apply Z.eqb_neq; exact KT).
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply (bn_div_fixed_top_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (PL := PL) (EA := EA)
               (dv := dv) (rm := rm) (num := num) (dvs := dvs) (adv := adv) (arm := arm) (anum := anum) (advs := advs) (ac := ac) (qc := qc);
        [exact PRE1 | reflexivity | exact EC | exact HAdv | exact HArm | exact HAnum | exact HAdvs | exact WRdv | exact HPrm | exact NROn | exact NROd
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | fold bd; exact (proj1 (Nat.le_succ_l 0 (bn_top bd)) (proj1 (Nat.neq_0_lt_0 _) (hide_elim _ KZ))) | fold bd; exact KT]. }
    cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW1 & PL1 & -> & CP1 & (EPL1 & ->)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP1) as (ENV1 & LS1').
    pose proof (cpost_refs LB PL EA lo B (bv_unsigned sp + -64) _ _ _ _ _ _ _ _ CP1) as RS1.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1087352)) with (Z_to_bv 64 1087352) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE1 CP1.

    pose proof (oref_at_stable _ _ _ _ _ _ _ RS1 HAdv) as HAdv1. pose proof (oref_at_stable _ _ _ _ _ _ _ RS1 HArm) as HArm1.
    rewrite div_fin_eq. cbn [embed interp]. apply implM_ret.
    clear ENV LS1 LS HEAP AUX ERR LAd LAd2 BNd ARRd MU WM HWL WOK HAdv HArm HAnum HAdvs RS1 PARTS WFS PWF IDS PLB ERRB ND HVdvs.
    match goal with FRx : rw_cells _ m2 _ _ |- _ => clear FRx end.

    lazymatch type of ENV1 with cenv _ _ _ _ _ _ _ _ _ _ ?fr _ _ _ _ =>
    assert (EPI : forall stE bsE mE OWE y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y28 y29 y30 y31,
               cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr stE bsE mE OWE -> lib_state bsE mE OWE PL EA ->
               evt bgusegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                              (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1) (tt, bsE) stE)
                 (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 1) y19 y20 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x1096e0) fc None mE (seg_rom bgusegs)))
    end.
    { intros stE bsE mE OWE y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y28 y29 y30 y31 ENVE LSE.
      pose proof (cenv_final LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ _ _ _ _ ENVE LSE)
        as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
      env_open ENVE.
      zstep. do 7 step.
      release_frame FRe STe (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists mE, OWE, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STe|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity. }

    lazymatch type of ENV1 with cenv _ _ _ _ _ _ _ _ _ _ ?fr _ _ _ _ =>
    assert (MID : forall bsM mM y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31,
               cenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m fr st1 bsM mM OW1 -> lib_state bsM mM OW1 PL EA ->
               oref_at bsM OW1 PL rm arm ->
               evt bgusegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                              (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1) (tt, octop rm bsM) st1)
                 (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) y5 y6 y7 sp (Z_to_bv 64 arm) y10 y11 y12 y13 y14 y15 y16 y17
                          y18 y19 y20 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x109788) fc None mM (seg_rom bgusegs)))
    end.
    { intros bsM mM y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 ENVM LSM HArmM.
      destruct rm as [r|]; cbn [octop oref_at] in *.
      - pose proof (HPrm r eq_refl) as HPr.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LSM) as PARTSM.
        pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ (proj1 ENVM) PARTSM HArmM HPr) as (RA0 & RAC & _ & _).
        assert (ARM : 0 < arm < 18446744073709551616) by (clear - RA0 RAC CEIL LO SPR; lia).
        zstep.
        zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (clear - ARM; lia). clear - K3 ARM. lia. }
        clear K3.
        do 2 zstep.
        eapply (ctop_call _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ st1 bsM mM OW1 r arm);
          [exact CEIL | exact GLO' | clear - LO; lia | exact FBsp | exact SPB | exact SPR2 | exact FROK | exact ENVM | exact LSM | exact HArmM | exact (hpl_wref PL r HPr) |].
        intros m5 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
        replace (ret_pc (Z_to_bv 64 1087384)) with (Z_to_bv 64 1087384) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zstep.
        eapply EPI; [exact ENV3| exact LS3].
      - subst arm.
        zstep.
        zstep. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
        clear K3.
        eapply EPI; [exact ENVM| exact LSM]. }
    destruct dv as [d|]; cbn [octop oref_at] in *.
    - pose proof (WRdv d eq_refl) as WRd.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS1') as PARTS1.
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ (proj1 ENV1) PARTS1 FROK HAdv1 (proj1 WRd)) as (VA0 & VAC & _).
      assert (ADV : 0 < adv < 18446744073709551616) by (clear - VA0 VAC CEIL LO SPR; lia).
      clear VAC PARTS1.
      unfold MallocRep.wz.
      zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
      clear K1.
      zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by (clear - ADV; lia). clear - K2 ADV. lia. }
      clear K2.
      do 2 zstep.
      eapply (ctop_call _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s bs OW m _ st1 bs1 m3 OW1 d adv);
        [exact CEIL | exact GLO' | clear - LO; lia | exact FBsp | exact SPB | exact SPR2 | exact FROK | exact ENV1 | exact LS1' | exact HAdv1 | exact WRd |].
      intros m4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2.
      replace (ret_pc (Z_to_bv 64 1087368)) with (Z_to_bv 64 1087368) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply MID; [exact ENV2| exact LS2| apply oref_at_setbn; exact HArm1].
    - subst adv.
      unfold MallocRep.wz.
      zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
      clear K1.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
      clear K2.
      eapply MID; [exact ENV1| exact LS1'| exact HArm1].
  Qed.
End Proofs.
End WithCeiling0.
