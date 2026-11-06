(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnDivWords BnDivLoop BnSpecs2 BnDivSpec.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnArith.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr DivModel.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface W_expand W_ctx BnLeaves BnUAlign BnCall W_small W_small2 W_top W_div_tail W_div.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].






Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_DIV : Z := 0x119298.
Definition BN_DIV_TOP_STACK : Z := 64 + BN_DIV_STACK.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  (* [comment removed for export] *)
  Lemma ctop_call : forall (POST : machine_state -> Prop) (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B SPv FB : Z)
      (s0 : PState) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem) (fr : list cell)
      (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= FB - 16 -> FB <= SPv -> SPv <= B -> SPv < 2^64 ->
    cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        cenv LB AD lo B SPv FB s0 ls0 OW0 m0 fr st (setbn r (bn_correct_top_pure (getbn r ls)) ls) m' OW ->
        lib_state (setbn r (bn_correct_top_pure (getbn r ls)) ls) m' OW AD EA ->
        evt usegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom usegs))) ->
    evt usegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_CORRECT_TOP) fc None m (seg_rom usegs)).
  Proof.
    intros until fc. intros CEIL GLO' LOFB FBSP SPB SPR ENV LS HA K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts st OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & _ & D0 & DC & DI & SEP). fold b in U, DC, DI, SEP.
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & AI).
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; lia).
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR. unfold BN_WORDS_MAX in OK3. unfold GLOBALS_TOP in GLO'.
    assert (UBD : ub_ptr_ok (Z.of_nat (bn_top b)) D).
    { unfold ub_ptr_ok. intros HT. unfold bn_arr in ARR. destruct (bn_d b) as [p|].
      - exact (block_ualign _ _ _ _ _ _ _ HEAP (proj1 ARR)).
      - exfalso. destruct ARR as [_ E]. unfold bn_dmax in OK2. rewrite E in OK2. cbn in OK2. lia. }
    eapply evt_cut.
    { eapply bn_correct_top_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact (ref_at_ualign _ _ _ _ _ _ _ _ HEAP ADB HA) | exact UBD | exact U | exact OK1 | exact OK2 | lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia | rewrite ESP; left; lia | exact SEPr | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    assert (U' : u64arr usegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; lia|]. split; [lia| exact I]. }
    eapply (rw_cells_transport usegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; lia|]; split; [right; lia| exact I]].
    eapply (rw_cells_transport usegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia|]; split; [lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls AD EA [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst]; lia|].
      constructor; [eapply (w_struct OW LB ls AD EA false [r] _ r ar); [left; reflexivity| exact HA| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib OW lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; exists (q, A, n); cbn; auto| constructor]. }
    assert (LS' : lib_state (setbn r (bn_correct_top_pure b) ls) m' OW AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW AD EA r ar); [| exact ND | exact HA | | |].
      - exact (lib_state_frame st LB [r] ls m m' OW AD EA _ HEAP LSH MUc WMc WOK).
      - exists D. split; [exact RES|]. unfold bn_arr in *. unfold bn_correct_top_pure, bn_dmax in *. cbn [bn_d bn_buf].
        destruct (bn_d b) as [p|]; [split; [exact (proj1 ARR)| exact U'] | exact ARR].
      - destruct (strip_top_spec (bn_buf b) (bn_top b) OK2) as (S1 & _ & _).
        unfold bn_okm, bn_correct_top_pure, bn_dmax, BN_WORDS_MAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [lia|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact IDS | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbn.
    eapply (cenv_silent LB AD lo B SPv FB s0 ls0 OW0 m0 CEIL ltac:(unfold GLOBALS_TOP; exact GLO') ltac:(lia) FBSP SPB fr fr);
      [exact ENV | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ].
  Qed.

  Lemma BN_div_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word) (dv rm num dvs : bnref) (adv arm anum advs : Z),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_DIV_TOP_STACK -> tp = wz RATP ->
    ref_at ls OW AD dv adv -> ref_at ls OW AD rm arm -> ref_at ls OW AD num anum -> ref_at ls OW AD dvs advs ->
    a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz (ad_ctx AD) ->
    nonpool dv -> nonpool rm -> nonpool num -> nonpool dvs -> dv <> num -> dv <> dvs ->
    implM usegs (interp (embed (BN_div (tree_ops bptr) dv rm num dvs ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun _ _ _ a0' => a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV) fc None m (seg_rom usegs)).
  Proof.
    intros until advs. intros PRE -> HAdv HArm HAnum HAdvs -> -> -> -> -> NPdv NPrm NPnum NPdvs NEdn NEdd.
    pose proof PRE as (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI).
    unfold BN_DIV_TOP_STACK, BN_DIV_STACK, BN_DIV, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold BN_div. rewrite bbind_get.
    set (bd := getbn dvs ls) in *.
    (* [comment removed for export] *)
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAdvs) as HVdvs.
    destruct (lib_state_open [] ls m OW AD EA dvs advs LS ND HAdvs ltac:(intros [])) as ((Dd & BNd & ARRd) & (OKd1 & OKd2 & OKd3 & OKd4) & _).
    fold bd in BNd, ARRd, OKd1, OKd2, OKd3, OKd4.
    destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB dvs Dd HVdvs ARRd) as (Ud & _ & Dd0 & DdC & DdI & _).
    fold bd in Ud, DdC, DdI.
    destruct (ref_at_inb _ _ _ _ _ ADB HAdvs) as (qd & Ad & nd & _ & Hind & Rd1 & Rd2).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hind) as (DA0 & _ & _ & DAC & DAI).
    destruct (proj1 (limbarr_limbs_at usegs m Dd (bn_buf bd)) Ud) as (LAd & _).
    unfold BN_WORDS_MAX in OKd3. unfold bn_cells in BNd. unfold MallocRep.wz in BNd. clear Ud.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR.
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 8 step. do 8 zstep.
    (* [comment removed for export] *)
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    eapply evt_cut.
    { eapply BN_is_zero_spec with (lo := lo) (A := advs) (D := Dd) (b := bd);
        [exact BNd | exact (ref_at_ualign _ _ _ _ _ _ _ _ HEAP ADB HAdvs) | unfold bn_dmax in *; lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI | rewrite ESP; left; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (? & ? & ? & a0z & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & E & MUc & WMc & MIc & STc & ->).
    subst ms'. rewrite ESP in *.
    replace (ret_pc (Z_to_bv 64 1151704)) with (Z_to_bv 64 1151704) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LAd2 : limbs_at usegs m2 Dd (bn_buf bd)).
    { eapply limbs_at_transport; [eapply limbs_at_transport; [exact LAd | exact MU |] | exact MUc |];
        cbn [disjoint_from]; fold (bn_dmax bd); (split; [left; lia| exact I]). }
    clear ST MI. transport_after_call usegs m1 m2 MUc WMc. clear MUc WMc.
    zstep. if_cases KZ; zify_cond KZ.
    2:{ (* [comment removed for export] *)
        ihere. to_implM.
        replace (bn_top bd =? 0)%nat with true by (destruct (bn_top bd =? 0)%nat; [reflexivity| exfalso; cbn in KZ; rewrite ?unsigned_lit in KZ by lia; lia]).
        unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
    apply Nat.eqb_neq in KZ.
    (* [comment removed for export] *)
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ HEAP ADB HAdvs) as (DAP & DA8).
    assert (HDD : exists pd, In (pd, Dd, 8 * Z.of_nat (bn_dmax bd)) OW).
    { unfold bn_arr in ARRd. destruct (bn_d bd) as [pd|]; [exists pd; exact (proj1 ARRd)|].
      exfalso. destruct ARRd as [_ E]. unfold bn_dmax in OKd2. rewrite E in OKd2. cbn in OKd2. lia. }
    destruct HDD as (pd & Hinpd).
    pose proof (block_ualign _ _ _ _ _ _ _ HEAP Hinpd) as (DDP & DD8).
    assert (RTOP : 0 < Z.of_nat (bn_top bd) < 8388609) by (unfold bn_dmax in *; lia).
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
    assert (Ntop : nth_error (bn_buf bd) (bn_top bd - 1) = Some dtop) by (apply nth_error_nth'; unfold bn_dmax in *; lia).
    assert (Rdtop : 0 <= dtop < 18446744073709551616).
    { assert (L : limb dtop) by (apply limbs_nth; exact OKd1). unfold limb in L. rewrite BW_lit in L. lia. }
    assert (RDD : Dd + 8 * Z.of_nat (bn_top bd) <= alloc_ceiling) by (unfold bn_dmax in *; lia).
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
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth usegs m2 Dd (bn_buf bd) (bn_top bd - 1) dtop ad LAd2 Ntop ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
    zstep. if_cases KT; zify_cond KT.
    { (* [comment removed for export] *)
      ihere. to_implM.
      replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact KZ).
      replace (dtop =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in KT by lia; lia).
      unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
    do 6 zstep.
    (* [comment removed for export] *)
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB [] ls m m2 OW AD EA _ HEAP LS MU WM WOK) as LS1.
    assert (FBlo : lo <= bv_unsigned sp + -64) by lia.
    assert (FBsp : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    assert (GLO' : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia).
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : cenv LB AD lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m fr s ls m2 OW)
    end.
    { unfold cenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia|].
      split; [exact STc|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MIc|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    pose proof (cenv_pre LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m CEIL GLO' FBlo FBsp SPB SPR2) as CPRE.
    pose proof (cenv_post LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m CEIL GLO' FBlo FBsp) as CPOST.
    pose proof (fun A => @bn_post_cpost _ _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) CEIL FBlo FBsp SPR2 A) as BPC.
    destruct (CPRE _ _ _ _ _ BN_DIV_STACK ENV LS1 ltac:(unfold BN_DIV_STACK; lia)) as (errv1 & PRE1).
    ihere. to_implM.
    replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact KZ).
    replace (dtop =? 0) with false by (symmetry; apply Z.eqb_neq; exact KT).
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implM_embed_bind.
    { eapply (bn_div_fixed_top_walk HM HF) with (lo := lo) (B := B) (errv := errv1) (OW := OW) (LB := LB) (AD := AD) (EA := EA)
               (dv := dv) (rm := rm) (num := num) (dvs := dvs) (adv := adv) (arm := arm) (anum := anum) (advs := advs);
        [exact PRE1 | reflexivity | exact HAdv | exact HArm | exact HAnum | exact HAdvs | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact NPdv | exact NPrm | exact NPnum | exact NPdvs | exact NEdn | exact NEdd | fold bd; lia | fold bd; exact KT]. }
    cbv beta. intros [u1 ls1] st1 ms1 PO. apply BPC in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & OW1 & -> & CP1 & ->).
    destruct (CPOST _ _ _ _ _ _ _ _ _ ENV CP1) as (ENV1 & LS1').
    pose proof (cpost_refs LB AD EA lo B (bv_unsigned sp + -64) _ _ _ _ _ _ _ _ CP1) as RS1.
    cbn [fst snd] in *.
    replace (ret_pc (Z_to_bv 64 1151908)) with (Z_to_bv 64 1151908) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear PRE1 CP1.
    (* [comment removed for export] *)
    pose proof (RS1 _ _ HAdv) as HAdv1. pose proof (RS1 _ _ HArm) as HArm1.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS1') as (_ & ADB1 & _ & _).
    destruct (ref_at_inb _ _ _ _ _ ADB1 HAdv1) as (qv & Av & nv & _ & Hinv & Rv1 & Rv2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV1) Hinv) as (VA0 & _ & _ & VAC & _).
    destruct (ref_at_inb _ _ _ _ _ ADB1 HArm1) as (qr & Ar & nr & _ & Hinr & Rr1 & Rr2).
    pose proof (RH_range _ _ _ _ _ _ _ (proj1 ENV1) Hinr) as (RA0 & _ & _ & RAC & _).
    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd embed interp]. apply implM_ret.
    unfold MallocRep.wz.
    zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
    clear K1.
    zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
    clear K2.
    do 2 zstep.
    eapply (ctop_call _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m _ st1 ls1 m3 OW1 dv adv);
      [exact CEIL | exact GLO' | lia | exact FBsp | exact SPB | exact SPR2 | exact ENV1 | exact LS1' | exact HAdv1 |].
    intros m4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2.
    replace (ret_pc (Z_to_bv 64 1151924)) with (Z_to_bv 64 1151924) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (lsa := setbn dv (bn_correct_top_pure (getbn dv ls1)) ls1) in *.
    zstep.
    zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
    clear K3.
    do 2 zstep.
    eapply (ctop_call _ LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m _ st1 lsa m4 OW1 rm arm);
      [exact CEIL | exact GLO' | lia | exact FBsp | exact SPB | exact SPR2 | exact ENV2 | exact LS2 | apply ref_at_setbn; exact HArm1 |].
    intros m5 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
    replace (ret_pc (Z_to_bv 64 1151940)) with (Z_to_bv 64 1151940) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof (cenv_final LB AD EA lo B (bv_unsigned sp) (bv_unsigned sp + -64) s ls OW m _ _ _ _ _ ENV3 LS3)
      as (F1 & F2 & F3 & (errvF & F4) & F5 & F6 & F7 & F8 & F9).
    env_open ENV3.
    do 2 zstep. do 7 step.
    release_frame FRe STe (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_post. do 15 eexists. exists m5, OW1, errvF. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact STe|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
