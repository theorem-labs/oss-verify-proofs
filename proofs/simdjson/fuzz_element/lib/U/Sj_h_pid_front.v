(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_alloc Sj_h_create Sj_h_active.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition SJ_PID : Z := 0x3ea60.
Definition SJ_PID_MID : Z := 0x3ead8.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition pid_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) : list cell :=
  [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sj_ro (m : mem) : Prop :=
  rw_cells usegs m SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)]
  /\ rw_cells usegs m SJ_IMPL_VT24 [C8 (Z_to_bv 64 SJ_CREATE_DPI)]
  /\ rw_cells usegs m SJ_DPI_VPTR dpi_vtable_cells.

Definition pid_front_X (PARSER : Z) : list (Z * Z) := [LXW_SJ; (PARSER + 8, PARSER + 16); (PARSER + 24, PARSER + 48)].

Definition pid_mid (ra0 : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B : Z) (m : mem) (SRET PARSER D len cap : Z) (nas : byte) (j57 : list byte)
    (psb ptp pim pix poc pia : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) SBUF TAPE IMPL IDX OC IA ws jsb jtp joc jia p12 p28 p50,
    ms' = MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 SRET) (Z_to_bv 64 (PARSER + 24)) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 len) (Z_to_bv 64 D) (Z_to_bv 64 PARSER) (Z_to_bv 64 (PARSER + 8)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 SJ_PID_MID) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (q + -80) /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96)
                 :: (ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) m'
    /\ lx_pres LB q (pid_front_X PARSER) m m'
    /\ sj_ro m' /\ sj_statics m' true
    /\ rw_cells usegs m' (q + -80) (pid_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8)
    /\ rw_cells usegs m' (PARSER + 8) [C8 (Z_to_bv 64 IMPL)]
    /\ rw_cells usegs m' (PARSER + 24) [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 cap)]
    /\ rw_cells usegs m' (PARSER + 48) (p48_cells nas j57 (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ rw_cells usegs m' IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) (Z_to_bv 64 0) p12 (Z_to_bv 64 IDX) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                            (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))
    /\ u32arr usegs m' IDX ws /\ length ws = Z.to_nat (roundup64 cap + 9)
    /\ rw_cells usegs m' SBUF [CB (Z.to_nat (roundup64 (5 * (cap / 3) + 64))) jsb]
    /\ rw_cells usegs m' TAPE [CB (Z.to_nat (8 * roundup64 (cap + 3))) jtp]
    /\ rw_cells usegs m' OC [CB (Z.to_nat 8192) joc] /\ rw_cells usegs m' IA [CB (Z.to_nat 1024) jia]
    /\ rblock_range SBUF (roundup64 (5 * (cap / 3) + 64)) /\ rblock_range TAPE (8 * roundup64 (cap + 3))
    /\ rblock_range IMPL 96 /\ rblock_range IDX (4 * (roundup64 cap + 9)) /\ rblock_range OC 8192 /\ rblock_range IA 1024.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma pid_front_cps : forall {A} (k : bptr -> bptr -> bptr -> bptr -> bptr -> bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (SRET PARSER D len : Z) (init : bool) (nas : byte) (j57 : list byte),
    RHEAP s LB m -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (80 + 64 + SJ_OPNEW_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    q <= PARSER -> PARSER + 80 <= B -> 0 <= len <= 2^26 ->
    sj_ro m -> sj_statics m init ->
    rw_cells usegs m (PARSER + 8) [C8 (Z_to_bv 64 0)] ->
    rw_cells usegs m (PARSER + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells usegs m (PARSER + 48) (p48_cells nas j57 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    (forall psb ptp pim pix poc pia s' ms',
        pid_mid ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m SRET PARSER D len (Z.max len 32) nas j57 psb ptp pim pix poc pia s' ms' ->
        implM usegs (k psb ptp pim pix poc pia) s' Q ms') ->
    implM usegs (mbind (newnt lops (roundup64 (5 * (Z.max len 32 / 3) + 64))) (fun sb => mbind (newnt lops (8 * roundup64 (Z.max len 32 + 3))) (fun tp =>
                 mbind (newnt lops 96) (fun im => mbind (newnt lops (4 * (roundup64 (Z.max len 32) + 9))) (fun ix =>
                 mbind (newnt lops 8192) (fun oc => mbind (newnt lops 1024) (fun ia => k sb tp im ix oc ia))))))) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SRET) (Z_to_bv 64 PARSER) (Z_to_bv 64 (PARSER + 24)) (Z_to_bv 64 D) (Z_to_bv 64 len) (Z_to_bv 64 0)
               a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_PID) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until j57. intros HEAP AUX QB ST CEIL GLO LO ERR MI Hq QP PB LEN (GOT & VT24 & VTD) SJS PIMPL DOCC P48 HK.
    unfold SJ_PID, SJ_OPNEW_STACK, RMALLOC_STACK, GLOBALS_TOP, p48_cells in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    change (2^26) with 67108864 in LEN.
    set (cap := Z.max len 32) in *. assert (CAP : 32 <= cap <= 67108864) by (subst cap; lia).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q (pid_front_X PARSER) a -> outside [(q - 80, q)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT. unfold SJ_IMPL_VT24, SJ_CREATE_DPI in VT24. unfold SJ_DPI_VPTR, dpi_vtable_cells in VTD.
    unfold implM. iprefix.
    step. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 10 step. do 8 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with |- evt _ ?QQ _ =>
      assert (GO : forall w8, w8 = Z_to_bv 64 cap -> evt usegs QQ
        (MS (mkR ra (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 SRET) (Z_to_bv 64 (PARSER + 24))
                 (Z_to_bv 64 32) (Z_to_bv 64 PARSER) (Z_to_bv 64 (PARSER + 24)) (Z_to_bv 64 D) (Z_to_bv 64 len) (Z_to_bv 64 0) a6 a7
                 (Z_to_bv 64 len) (Z_to_bv 64 D) (Z_to_bv 64 PARSER) s5 (Z_to_bv 64 0) s7 w8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3eab4) fc None m1 (seg_rom usegs))) end.
    2:{ if_cases K; zify_cond K.
        - rewrite ?unsigned_lit in K by lia.
          eapply evt_eq; [| eapply (GO (Z_to_bv 64 len))]; [cbv delta [mkR]; reflexivity| f_equal; subst cap; lia].
        - rewrite ?unsigned_lit in K by lia. step.
          eapply evt_eq; [| eapply (GO (Z_to_bv 64 32))]; [cbv delta [mkR]; reflexivity| f_equal; subst cap; lia]. }
    intros w8 ->.

    step. step. step. if_true. step. step.
    if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    step. step.
    if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.

    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HEAP2 : RHEAP s LB m2).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES2 : lx_pres LB q (pid_front_X PARSER) m m2) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
    assert (SJS2 : sj_statics m2 init).
    { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS].
      intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
    clear MU WM SJS.
    ihere. to_implM.
    eapply (allocate_cps HM) with (B := B) (lo := lo) (DOC := PARSER + 24) (cap := cap);
      [exact HEAP2| exact AUX2| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia| lia
      | change (2^26) with 67108864; lia| exact GOT| exact DOCC|].
    intros psb ptp s3' ms3 PO. unfold hpost in PO.
    destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3
                    & -> & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
    unfold allocate_R in RR. destruct RR as (SBUF & TAPE & jsb & jtp & -> & HEAP3 & PRES23 & DOCC3 & BLKSB & BLKTP & BRSB & BRTP).
    replace (ret_pc (Z_to_bv 64 256792)) with (Z_to_bv 64 256792) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in PIMPL; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in P48; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in GOT;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AG) in VT24;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AG) in VTD;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    assert (SJS3 : sj_statics m3 init).
    { eapply sj_statics_agree; [exact AG| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|].
      unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. lia. }
    assert (PRES3 : lx_pres LB q (pid_front_X PARSER) m m3).
    { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_weaken; [exact PRES23| lia| auto|].
      intros a Ha. unfold pid_front_X. cbn [rin_ivs fst snd] in Ha |- *. clear - Ha. lia. }
    clear AG PRES2 PRES23 HEAP2 AUX2 SJS2.
    pose proof BRSB as (SB0 & _ & _ & SBC & SBS). pose proof BRTP as (TP0 & _ & _ & TPC & TPS).
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in SBC, TPC.
    pose proof (roundup64_ge (5 * (cap / 3) + 64)) as NSB1. pose proof (roundup64_ge (cap + 3)) as NTP1.
    assert (D3 : 0 <= cap / 3) by (apply Z.div_pos; lia).
    pose proof (munch_refl [(q - 80, q)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    unfold implM. iprefix.

    step. step. step. if_true. step.
    eapply evt_cut.
    { eapply (getact_spec) with (lo := lo) (init := init); [exact ST3| unfold GLOBALS_TOP; lia| lia| lia| assumption| exact SJS3]. }
    intros ms' PO. unfold getact_post in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & SJS4).
    unfold SJ_STATICS_LO, SJ_STATICS_HI in MU4.
    replace (ret_pc (Z_to_bv 64 257156)) with (Z_to_bv 64 257156) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (HEAP4 : RHEAP s3' ((ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) m4).
    { eapply LH_frame; [eapply LH_frame; [exact HEAP3| exact MU| exact WM|]| exact MU4| exact WM4|].
      - constructor; [apply W_ok_stack; cbn; lia| constructor].
      - constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|]| exact MU4| exact WM4|].
      - constructor; [cbn; unfold RAUXV_CELL; lia| constructor].
      - constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES4 : lx_pres LB q (pid_front_X PARSER) m m4).
    { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_trans; eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI| exact MU4| exact WM4|].
      intros a Ha [HX HC]. unfold pid_front_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
      split; [| split; [lia| exact I]]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in PIMPL; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO QP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in DOCC3; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO QP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in P48; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO QP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in GOT; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in VT24; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in VTD; [| intros a Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in ERR3; [| intros a Ha; rewrite ELX in Ha; cbn in Ha; cbn [outside]; clear - Ha LO GLO; lia].
    pose proof (rw_cells_bound _ _ _ _ BLKSB) as BB1. cbn [cells_size csize Nat.add] in BB1.
    pose proof (rw_cells_bound _ _ _ _ BLKTP) as BB2. cbn [cells_size csize Nat.add] in BB2.
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKSB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; clear - Ha LO GLO SBC SBS CEIL NSB1 D3 CAP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKTP; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; clear - Ha LO GLO TPC TPS CEIL NTP1 CAP; lia].
    clear AG MU WM MU4 WM4 PRES3 HEAP3 AUX3 SJS3.
    pose proof (munch_refl [(q - 80, q)]%Z m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    pose proof (proj1 SJS4) as SJC. unfold sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC, MallocRep.wz in SJC.

    unfold SJ_ACTIVE_IMPL.

    step. step. zstep. step. step. if_false. step. if_false. do 6 step.
    ihere. to_implM.
    eapply (create_cps HM) with (B := B) (lo := lo) (DST := PARSER + 8) (cap := cap);
      [exact HEAP4| exact AUX4| lia| exact ST4| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| exact ERR3| exact MI4| lia| lia| lia
      | change (2^26) with 67108864; lia| exact GOT| exact VTD| exact PIMPL|].
    intros pim pix poc pia s5' ms5 PO. unfold hpost in PO.
    destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5
                    & -> & MI5 & ST5 & (errv5 & ERR5) & AUX5 & FA5 & SO5 & RR).
    unfold create_R in RR.
    destruct RR as (IMPL & IDX & OC & IA & ws & joc & jia & p12 & p28 & p50 & -> & HEAP5 & PRES45 & DSTC & THISC & ARR & LWS & BLKOC & BLKIA & BRIM & BRIX & BROC & BRIA).
    replace (ret_pc (Z_to_bv 64 257204)) with (Z_to_bv 64 257204) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES45) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in DOCC3; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in P48; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG) in GOT;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AG) in VT24;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AG) in VTD;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKSB;
      [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [cbn [rin_ivs fst snd]; clear - Ha SBC CEIL LO QP NSB1 D3 CAP; lia|
          right; left; exists (psb, SBUF, roundup64 (5 * (cap / 3) + 64)); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; clear - Ha NSB1 D3 CAP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ AG) in BLKTP;
      [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [cbn [rin_ivs fst snd]; clear - Ha TPC CEIL LO QP NTP1 CAP; lia|
          right; left; exists (ptp, TAPE, 8 * roundup64 (cap + 3)); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; clear - Ha NTP1 CAP; lia]]].
    assert (SJS5 : sj_statics m5 true).
    { eapply sj_statics_agree; [exact AG| | exact SJS4]. intros a Ha. apply sjs_addr_client; [exact Ha|].
      unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. lia. }
    pose proof (LH_head_disj _ _ _ _ _ _ HEAP4) as DJTP.
    pose proof (LH_head_disj _ _ _ _ _ _ (RHEAP_pull _ [(ptp, TAPE, 8 * roundup64 (cap + 3))] _ _ _ HEAP4)) as DJSB.
    assert (PRES5 : lx_pres LB q (pid_front_X PARSER) m m5).
    { eapply lx_pres_trans; [exact PRES4|].
      eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      eapply (lx_pres_sub LB q _ _ _ _ _ _ PRES45); [lia| intros b Hb; right; right; exact Hb|].
      intros a Ha NX. exfalso. apply NX. unfold pid_front_X. cbn [rin_ivs fst snd] in Ha |- *. clear - Ha. lia. }
    clear AG PRES4 PRES45 MU WM HEAP4 AUX4 SJC.
    pose proof (munch_refl [(q - 80, q)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.

    step. step. if_false. step. step. if_false. step. if_false. step. step. if_true.
    ihere. to_implM. apply HK. unfold pid_mid.
    do 16 eexists. exists m5, errv5, SBUF, TAPE, IMPL, IDX, OC, IA, ws, jsb, jtp, joc, jia, p12, p28, p50.
    split; [cbv delta [mkR SJ_PID_MID]; reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact ERR5|]. split; [exact AUX5|].
    split; [congruence|]. split; [congruence|]. split; [exact HEAP5|]. split; [exact PRES5|].
    split. { unfold sj_ro, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, SJ_IMPL_VT24, SJ_CREATE_DPI, SJ_DPI_VPTR, dpi_vtable_cells. auto. }
    split; [exact SJS5|]. split; [unfold pid_frame; exact FR|]. split; [exact DSTC|]. split; [exact DOCC3|]. split; [unfold p48_cells; exact P48|].
    split; [exact THISC|]. split; [exact ARR|]. split; [exact LWS|]. split; [exact BLKSB|]. split; [exact BLKTP|]. split; [exact BLKOC|]. split; [exact BLKIA|].
    auto 8.
  Qed.
End Proofs.
End WithCeiling0.

