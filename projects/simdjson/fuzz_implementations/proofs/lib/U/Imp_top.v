(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog ImpImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_h_arith.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Pj_loc_defs Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_active Sj_h_pid_front.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_stage2_iface Printf_mlib Imp_defs Imp_kit Imp_iface Imp_lftoi1 Imp_lftoi2 Imp_lftoi3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HS2 : stage2t_stmt.
  Hypothesis OKARM : imp_okarm_stmt.

  Theorem rfuzz_one_premise : rfuzz_one_stmt.
  Proof.
    unfold rfuzz_one_stmt. intros until canary.
    intros HEAP LXS SJS VEC AEXT SEW SSP AUX SPB B62 ST CEIL GLO LO ERR TP MI AL16 PL FRM -> ->.
    unfold LX_FUZZ, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    set (q0 := bv_unsigned sp) in *. clearbody q0. subst sp.
    subst tp. replace (errno_addr (Z_to_bv 64 RATP)) with 1004708 in ERR by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    remember (q0 - 1056) as q eqn:EQ. replace q0 with (q + 1056) in * by lia. clear EQ q0.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    set (len := zlength d) in *.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] a -> outside [(q, q + 1056)]%Z a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    unfold ImpModel.fuzz_one, ImpModel.fuzz_one_with. fold len.
    assert (ALq : q mod 16 = 0) by (replace q with (q + 1056 + (-66) * 16) by lia; rewrite Z.mod_add by lia; exact AL16).
    pose proof (munch_refl [(q, q + 1056)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    Ltac tr1 AG H tac := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; cbn in Ha; tac].
    unfold implM. iprefix.

    step. carve_frame 1056%nat ST. replace (q + 0) with q in * by lia.
    apply (rw_cells_split_CB usegs _ _ [] 1056 junk [] [8;40;8;264;544;88;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 13 hstep. hstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    split_cells FR 1%nat F0 FR1. split_cells FR1 1%nat F16 FR2. split_cells FR2 1%nat F48 FR3. split_cells FR3 1%nat F40 FR4. split_cells FR4 1%nat FIMP FR5. split_cells FR5 1%nat F848 F936.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG01.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (LXS1 : lx_statics m1).
    { eapply lx_statics_agree; [exact AG01| | exact LXS]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I]. }
    assert (SJS1 : sj_statics m1 (match v with Some _ => true | None => false end)).
    { eapply sj_statics_agree; [exact AG01| | exact SJS]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I]. }
    assert (VEC1 : imp_vec m1 LB v).
    { eapply imp_vec_agree; [exact AG01| | | exact VEC].
      - intros a Ha. pose proof (impvec_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I].
      - intros a Ha. specialize (BLB a Ha). cbn [outside]. split; [lia| exact I]. }
    assert (AEX1 : aex_tbl m1 (match v with Some _ => 3 | None => 2 end)).
    { eapply aex_tbl_agree; [exact AG01| | exact AEXT]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. cbn [outside]. split; [lia| exact I]. }
    assert (PRES01 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into ST1 end. lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells _ m1 1004708 _ |- _ => rename H into ERR1 end.
    clear AG01.

    destruct v as [p|].
    -
      destruct VEC1 as (A & INA & VC & AW). unfold imp_vec_cells, IMP_VEC_LO in VC. unfold MallocRep.wz in VC, AW.
      pose proof (LH_block_range _ _ _ _ HEAP1 INA) as (A0 & A16 & _ & AC & AS). cbn [blk_addr blk_size fst snd] in A0, AC, AS. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
      step. step. step. if_false.

      call (lftoi_setup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ q lo A _ _);
        [exact ST1| unfold GLOBALS_TOP; lia| lia| exact MI1| lia| unfold IMP_FRAME; lia| exact LXS1| exact VC| exact AW| lia| lia| exact A16| unfold IMP_FRAME; lia| exact F16| exact F48| exact FIMP| ].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      lazymatch goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end. lazymatch goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG02.
      ihere. to_implM.
      apply (ImpImpl.implM_imp_static_some usegs raw_malloc raw_free ps_so set_so_ps p). cbn [bind ret lib_malloc lib_free lops Target.ops].
      change (implM usegs (body_prog (sj_root_copy d) len p) s
                (rfuzz_one_post ra (Z_to_bv 64 (q + 1056)) gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d (Some p) lo B canary m))
        with (implM usegs (body_prog (sj_root_copy d) len p) s
                (rfuzz_one_post ra (Z_to_bv 64 (q + IMP_FRAME)) gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d (Some p) lo B canary m)).
      eapply (lftoi_body HM HF HS2 OKARM false) with (OW' := []);
        [exact FRM| exact MI2| exact ST2| eassumption| | reflexivity| reflexivity| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| exact ALq| unfold IMP_FRAME; lia| exact B62
        | exact HEAP| exact LXS| exact SEW| exact SSP| exact PL| | split; reflexivity| | | | | | eassumption| eassumption| eassumption| eassumption
        | do 4 eexists; eassumption| do 4 eexists; eassumption| do 4 eexists; eassumption| eassumption| exact F936].
      + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      + cbn [app]. eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + exists A. split; [exact INA| split; [exact VC| exact AW]].
      + cbn [sj_staticsB]. eapply sj_statics_agree; [exact AG02| | exact SJS]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I].
      + eapply aex_tbl_agree; [exact AG02| | exact AEXT]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. cbn [outside]. split; [lia| exact I].
      + eapply lx_statics_agree; [exact AG02| | exact LXS]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I].
      + unfold IMP_FRAME. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
    -
      pose proof (imp_vec_none_cells _ _ VEC1) as VC. unfold IMP_VEC_LO in VC.
      step. step. step. if_true. clear VC MU WM.
      ihere. to_implM.
      apply (ImpImpl.implM_imp_static_none usegs raw_malloc raw_free ps_so set_so_ps). cbn [bind ret lib_malloc lib_free lops Target.ops].
      change (newnt (Target.ops raw_malloc raw_free ps_so set_so_ps) IMP_VEC) with (newnt lops IMP_VEC).

      pose proof (lftoi_first HM (fun p => body_prog (sj_root_copy d) len p)) as LF.
      pose proof (LF (rfuzz_one_post ra (Z_to_bv 64 (q + IMP_FRAME)) gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d None lo B canary m)) as LF2.
      eapply LF2 with (B := B) (lo := lo); clear LF LF2;
        [exact HEAP1| exact AUX1| lia| exact ST1| exact CEIL'| unfold GLOBALS_TOP; lia| unfold IMP_FIRST_STACK, Imp_gsi.IMP_GRSI_STACK, RMALLOC_STACK; lia
        | eassumption| exact MI1| lia| exact LXS1| exact SJS1| exact VEC1| exact AEX1|].
      intros p s' ms' FP. unfold first_post in FP.
      destruct FP as (y1 & w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m2 & errv2
                      & -> & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & (A & HEAP2 & BR & VC & AW & SJM & AEX2 & PRES12)).
      cbv beta. assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR2.
      pose proof BR as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES12) as AG12.
      Ltac o12 := split; [unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; lia| left; lia].
      tr1 AG12 F0 o12. tr1 AG12 F16 o12. tr1 AG12 F48 o12. tr1 AG12 F40 o12. tr1 AG12 FIMP o12. tr1 AG12 F848 o12. tr1 AG12 F936 o12.
      assert (LXS2 : lx_statics m2).
      { eapply lx_statics_agree; [exact AG12| | exact LXS1]. intros a Ha. apply lxs_addr_client; [exact Ha|]. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1.
        unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
        unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha R1. lia. }
      assert (PRES02 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m m2).
      { eapply lx_pres_trans; [exact PRES01|]. eapply lx_pres_weaken; [exact PRES12| lia| intros b Hb; exact Hb| intros a Ha; exact Ha]. }
      clear AG12 PRES12 HEAP1 AUX1 LXS1 SJS1 VEC1 AEX1 MI1 ST1 ERR1 PRES01.
      unfold imp_vec_cells, IMP_VEC_LO in VC. unfold MallocRep.wz in VC, AW.
      pose proof (munch_refl [(q, q + 1056)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.
      call (lftoi_setup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ q lo A _ _);
        [exact ST2| unfold GLOBALS_TOP; lia| lia| exact MI2| lia| unfold IMP_FRAME; lia| exact LXS2| exact VC| exact AW| lia| lia| exact A16| unfold IMP_FRAME; lia| exact F16| exact F48| exact FIMP| ].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      lazymatch goal with H : stk _ m3 _ _ |- _ => rename H into ST3 end. lazymatch goal with H : mem_inv _ m3 |- _ => rename H into MI3 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG23.
      ihere. to_implM.
      eapply (lftoi_body HM HF HS2 OKARM true) with (OW' := [(p, A, 8)]);
        [exact FRM| exact MI3| exact ST3| eassumption| | exact FA2| exact SO2| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| exact ALq| unfold IMP_FRAME; lia| exact B62
        | exact HEAP| exact LXS| exact SEW| exact SSP| exact PL| | exists A; reflexivity| | | | | | eassumption| eassumption| eassumption| eassumption
        | do 4 eexists; eassumption| do 4 eexists; eassumption| do 4 eexists; eassumption| eassumption| exact F936].
      + eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      + cbn [app]. eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + exists A. split; [left; reflexivity| split; [exact VC| exact AW]].
      + cbn [sj_staticsB]. eapply sj_statics_mid_agree; [exact AG23| | exact SJM]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I].
      + eapply aex_tbl_agree; [exact AG23| | exact AEX2]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. cbn [outside]. split; [lia| exact I].
      + eapply lx_statics_agree; [exact AG23| | exact LXS2]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. split; [lia| exact I].
      + unfold IMP_FRAME. eapply lx_pres_trans; [exact PRES02|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI].
  Qed.
End Proofs.
End WithCeiling0.
