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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_alloc Sj_h_create Sj_h_active Sj_h_pid_front.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Sj_h_parse Atp_pid_parse0 Atp_pid.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma pid_null_cps : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra0 gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q : Z)
      (F : bvmap 5 word) (fc : bv 32) (s00 : PState) (LB : list block) (lo B : Z) (m00 : mem) (SRET PARSER : Z) (j57 : list byte)
      (psb ptp pim pix poc pia : bptr) (s : PState) (ms : machine_state) (jr0 jr8 jr16 jr20 : list byte),
    pid_mid ra0 q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LB lo B m00 SRET PARSER 0 0 32 (Z_to_bv 8 0) j57 psb ptp pim pix poc pia s ms ->
    RHEAP s00 LB m00 -> frm0 fc -> q <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - (80 + 32 + SJ_S2_STACK) -> 0 <= q < 2^64 ->
    q <= SRET -> SRET + 24 <= PARSER -> PARSER + 80 <= B -> PARSER mod 8 = 0 ->
    rw_cells usegs m00 SRET [CB 8 jr0; CB 8 jr8; CB 4 jr16; CB 4 jr20] ->
    (forall s' ms',
        (exists IMPL IDX OC IA TAPE SBUF,
          hpostF ra0 q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 lo B
            (pidn_R ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 32 + 9)) :: (pim, IMPL, 96)
                      :: (ptp, TAPE, 8 * roundup64 (32 + 3)) :: (psb, SBUF, roundup64 (5 * (32 / 3) + 64)) :: LB)
                   LB q SRET PARSER m00 (Z_to_bv 8 0) j57 jr20 IMPL IDX OC IA TAPE SBUF 32) s' ms') ->
        implM usegs k s' Q ms') ->
    implM usegs k s Q ms.
  Proof.
    intros A k Q. intros until jr20. intros MID HEAP00 FRM QB B63 CEIL GLO LO Hq QS SP PBB ALP SRETC HK.
    unfold pid_mid in MID.
    destruct MID as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & errv & SBUF & TAPE & IMPL & IDX & OC & IA & ws & jsb & jtp & joc & jia
                     & p12 & p28 & p50 & -> & MI & ST & ERR & AUX & FA & SO & HEAP & PRES0 & (GOT & VT24 & VTD) & SJS & FR & PIMPL & DOCC & P48 & THISC & ARR & LWS
                     & BLKSB & BLKTP & BLKOC & BLKIA & BRSB & BRTP & BRIM & BRIX & BROC & BRIA).
    unfold SJ_PID_MID, SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK, GLOBALS_TOP, p48_cells, pid_frame in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES0)) in SRETC;
      [| intros a Ha; cbn in Ha; split; [unfold pid_front_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; clear - Ha SP QS LO GLO; lia| left; lia]].
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    unfold SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in GOT. unfold SJ_IMPL_VT24, SJ_CREATE_DPI in VT24. unfold SJ_DPI_VPTR, dpi_vtable_cells in VTD.
    unfold impl_cells16, SJ_DPI_VPTR in THISC.
    pose proof BRIM as (IM0 & _ & _ & IMC & IMS). pose proof BRIX as (IX0 & _ & _ & IXC & _). pose proof BRSB as (SB0 & _ & _ & SBC & _).
    pose proof BRTP as (TP0 & _ & _ & TPC & _). pose proof BROC as (OC0 & _ & _ & OCC & _). pose proof BRIA as (IA0 & _ & _ & IAC & _).
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in IMC, IXC, SBC, TPC, OCC, IAC.
    pose proof (roundup64_ge 32) as RC1. pose proof (roundup64_ge (32 + 3)) as RC2. pose proof (roundup64_ge (5 * (32 / 3) + 64)) as RC3.
    pose proof (roundup64_lt 32) as RC4. pose proof (roundup64_lt (32 + 3)) as RC5. pose proof (roundup64_lt (5 * (32 / 3) + 64)) as RC6.
    hide BLKSB. hide BLKTP. hide BLKOC. hide BLKIA. hide ARR.
    pose proof (munch_refl [(q - 80, q); (IMPL, IMPL + 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.

    step. if_true. step. step. if_true.
    step. step. step. if_false. step. step.
    if_cases KI; zify_cond KI; [exfalso; rewrite ?unsigned_lit in KI by lia; lia|]. clear KI.
    zstep. step. rewrite (land7_aligned IMPL) by (destruct BRIM as (? & AL16 & _); first [lia| exact AL16]). if_false.
    step. hstep. do 5 step.
    replace (ret_pc (Z_to_bv 64 SJ_DPI_PARSE)) with (Z_to_bv 64 SJ_DPI_PARSE) by (symmetry; apply ret_pc_even; [unfold SJ_DPI_PARSE; lia| reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 32 + 9))] _ _ _ HEAP) as HEAPIM. cbn [app] in HEAPIM.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    unhide BLKSB. apply (rw_cells_agree _ _ _ _ _ AG) in BLKSB.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 4 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP SBC CEIL LO; lia. }
    unhide BLKTP. apply (rw_cells_agree _ _ _ _ _ AG) in BLKTP.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 3 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP TPC CEIL LO; lia. }
    unhide BLKOC. apply (rw_cells_agree _ _ _ _ _ AG) in BLKOC.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 1 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP OCC CEIL LO; lia. }
    unhide BLKIA. apply (rw_cells_agree _ _ _ _ _ AG) in BLKIA.
    2:{ intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP IAC CEIL LO; lia. }
    unhide ARR. apply (u32arr_agree _ _ _ _ _ AG) in ARR.
    2:{ intros a Ha; rewrite LWS in Ha; cbn [outside]. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 2 right; left; reflexivity)) as SEP.
        repeat split; clear - Ha SEP IXC CEIL LO; lia. }
    assert (SJS5 : sj_statics m5 true).
    { eapply sj_statics_agree; [exact AG| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
      cbn [outside]; repeat split; clear - Ha IMS CEIL LO GLO; lia. }
    assert (HEAP5 : RHEAP s ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 32 + 9)) :: (pim, IMPL, 96)
                      :: (ptp, TAPE, 8 * roundup64 (32 + 3)) :: (psb, SBUF, roundup64 (5 * (32 / 3) + 64)) :: LB) m5).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, IMPL, 96)); [do 3 right; left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX5 : rauxv_ok m5 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; clear - IMS IMC CEIL LO QB; lia| constructor]. }
    pose proof (LH_head_disj _ _ _ _ _ _ HEAPIM) as DJIM.
    assert (PRES5 : lx_pres LB q (pidn_X SRET) m m5).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [outside]. split; [| split; [| exact I]].
      - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - destruct HC as [HC|[HC|HC]]; [lia| | clear - HC IMS; lia].
        apply DJIM. eapply in_block_incl; [| exact HC]. intros b Hb. cbn [app]. do 5 right. exact Hb. }
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPIM ltac:(do 2 right; left; reflexivity)) as D_IM_IX.
    clear AG MU WM HEAP AUX HEAPIM DJIM.
    ihere. to_implM.
    eapply (parse0_cps) with (B := B) (lo := lo) (THIS := IMPL) (DOC := PARSER + 24) (IDX := IDX) (BUF := 0) (TAPE := TAPE) (SBUF := SBUF) (OC := OC) (IA := IA)
                             (ws0 := ws) (cap := 32) (tcap := roundup64 (32 + 3)) (scap := roundup64 (5 * (32 / 3) + 64)).
    - rewrite LWS. change (roundup64 32) with 64. lia.
    - exact HEAP5.
    - exact AUX5.
    - lia.
    - exact B63.
    - exact ST.
    - exact CEIL'.
    - unfold GLOBALS_TOP. lia.
    - unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK. lia.
    - rewrite ELX. exact ERR.
    - assumption.
    - lia.
    - exists (pim, IMPL, 96). split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
    - exists (pix, IDX, 4 * (roundup64 32 + 9)). split; [do 2 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; rewrite LWS; change (roundup64 32) with 64; lia].
    - unfold ivl_disj. cbn [fst snd]. rewrite LWS. change (roundup64 32) with 64 in *. clear - D_IM_IX. lia.
    - lia.
    - lia.
    - apply mod4_of_mod16. destruct BRIX as (_ & AL16 & _). exact AL16.
    - unfold impl_cells16, SJ_DPI_VPTR. exact THISC.
    - exact ARR.
    - intros s6' ms6 PO. unfold hpost in PO.
      destruct PO as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m6
                      & -> & MI6 & ST6 & (errv6 & ERR6) & AUX6 & FA6 & SO6 & RR).
      unfold parse0_R in RR. destruct RR as (HEAP6 & PRES56 & (nsi6 & nxt6 & docv6 & THISC6) & ->).
      replace (ret_pc (Z_to_bv 64 257088)) with (Z_to_bv 64 257088) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      set (tcap := roundup64 (32 + 3)) in *. set (scap := roundup64 (5 * (32 / 3) + 64)) in *.
      assert (LWZ : 4 * Z.of_nat (length ws) = 4 * (roundup64 32 + 9)) by (rewrite LWS; lia).
      assert (XLOW : forall a, rin_ivs (parse_X IMPL IDX TAPE SBUF OC IA (Z.of_nat (length ws)) tcap scap) a -> a < alloc_ceiling).
      { intros a Ha. unfold parse_X in Ha. cbn [rin_ivs fst snd] in Ha. clear - Ha IMC IXC TPC SBC OCC IAC LWZ. lia. }
      assert (XSTAT : forall a, 0xd6000 <= a < 0x111000 -> ~ rin_ivs (parse_X IMPL IDX TAPE SBUF OC IA (Z.of_nat (length ws)) tcap scap) a).
      { intros a Ha Hx. unfold parse_X in Hx. cbn [rin_ivs fst snd] in Hx.
        destruct BRIX as (_ & _ & _ & _ & IXS). destruct BRSB as (_ & _ & _ & _ & SBS). destruct BRTP as (_ & _ & _ & _ & TPS).
        destruct BROC as (_ & _ & _ & _ & OCS). destruct BRIA as (_ & _ & _ & _ & IAS).
        destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]]; [clear - Ha Hx IMS| clear - Ha Hx IXS LWZ| clear - Ha Hx TPS| clear - Ha Hx SBS| clear - Ha Hx OCS| clear - Ha Hx IAS];
          lia. }
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES56) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in PIMPL; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in DOCC; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in P48; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in SRETC; [| intros a Ha; cbn in Ha; split; [intros Hx; apply XLOW in Hx; clear - Ha Hx CEIL LO QS SP; lia| left; lia]].
      assert (STCL : forall a, 0xd6000 <= a < 0x111000 -> ~ ralloc_static a ->
                lx_client ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 32 + 9)) :: (pim, IMPL, 96) :: (ptp, TAPE, 8 * tcap) :: (psb, SBUF, scap) :: LB)
                          (q + -80) (parse_X IMPL IDX TAPE SBUF OC IA (Z.of_nat (length ws)) tcap scap) a).
      { intros a Ha Hs. split; [apply XSTAT; exact Ha| right; right; split; assumption]. }
      apply (rw_cells_agree _ _ _ _ _ AG) in GOT;
        [| intros a Ha; cbn in Ha; apply STCL; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in VTD;
        [| intros a Ha; cbn in Ha; apply STCL; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG) in VT24;
        [| intros a Ha; cbn in Ha; apply STCL; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]].
      assert (SJS6 : sj_statics m6 true).
      { eapply sj_statics_agree; [exact AG| | exact SJS5]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 R2]. apply STCL; [unfold GLOBALS_TOP in R1; lia| exact R2]. }
      assert (PRES6 : lx_pres LB q (pidn_X SRET) m m6).
      { eapply lx_pres_trans; [exact PRES5|].
        eapply (lx_pres_sub LB q _ _ _ _ _ _ PRES56); [lia| intros b Hb; do 6 right; exact Hb|].
        intros a Ha _. split; [apply XLOW in Ha; clear - Ha CEIL LO; lia|]. split; [| intros Hs; exact (XSTAT a Hs Ha)].
        intros IB. unfold parse_X in Ha. cbn [rin_ivs fst snd] in Ha.
        pose proof (RHEAP_prefix_disj _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, 4 * (roundup64 32 + 9)); (pim, IMPL, 96); (ptp, TAPE, 8 * tcap); (psb, SBUF, scap)] LB _ HEAP6) as PD.
        destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[]]]]]]].
        - apply (PD (pim, IMPL, 96) ltac:(do 3 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (pix, IDX, 4 * (roundup64 32 + 9)) ltac:(do 2 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (ptp, TAPE, 8 * tcap) ltac:(do 4 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (psb, SBUF, scap) ltac:(do 5 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (poc, OC, 8192) ltac:(do 1 right; left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia.
        - apply (PD (pia, IA, 1024) ltac:(left; reflexivity) a IB). cbn [blk_addr blk_size fst snd]. lia. }
      clear AG PRES5 PRES56 HEAP5 AUX5 SJS5 XLOW XSTAT STCL THISC BLKSB BLKTP BLKOC BLKIA ARR D_IM_IX.
      unfold impl_cells16 in THISC6.
      pose proof (munch_refl [(q - 80, q); (SRET, SRET + 24)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      unfold implM. iprefix.

      step. step. if_false. step. if_false.
      step. if_cases KS; zify_cond KS; [exfalso; rewrite ?unsigned_lit in KS by lia; lia|]. clear KS.
      hstep. hstep. step. step.
      do 11 step. release_frame FR ST6 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (HEAP7 : RHEAP s6' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 32 + 9)) :: (pim, IMPL, 96)
                                        :: (ptp, TAPE, 8 * tcap) :: (psb, SBUF, scap) :: LB) mx)
            by (eapply LH_frame; [exact HEAP6| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; lia|]; constructor; [apply W_ok_stack; cbn; lia| constructor]);
          assert (AUX7 : rauxv_ok mx B)
            by (eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]);
          assert (SJS7 : sj_statics mx true)
            by (eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS6]; intros a Ha; unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha;
                cbn [outside]; repeat split; clear - Ha LO GLO QS; lia);
          assert (PRES7 : lx_pres LB q (pid_front_X PARSER ++ pidn_X SRET) m00 mx)
            by (eapply lx_pres_trans; [eapply lx_pres_weaken; [exact PRES0| apply Z.le_refl| intros b0 Hb0; exact Hb0| intros a Ha; apply in_or_rin_app_l; exact Ha]|];
                eapply lx_pres_weaken; [eapply lx_pres_trans; [exact PRES6| eapply lx_pres_of_munch; [exact MU| exact WM|]]| apply Z.le_refl| intros b0 Hb0; exact Hb0| intros a Ha; apply in_or_rin_app_r; exact Ha];
                intros a Ha [HX HC]; unfold pidn_X in HX; cbn [rin_ivs fst snd] in HX; cbn [outside]; split; [| split; [clear - HX; lia| exact I]];
                destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia])
      end.
      ihere. to_implM. apply HK. exists IMPL, IDX, OC, IA, TAPE, SBUF. unfold hpostF. do 15 eexists. eexists F, fc, _.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FRM|]. split; [eassumption|]. split; [exact ST6|]. split; [exists errv6; eassumption|].
      split; [exact AUX7|]. split; [congruence|]. split; [congruence|].
      unfold pidn_R. split; [exact HEAP7|]. split; [exact PRES7|].
      split; [unfold sj_ro, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, SJ_IMPL_VT24, SJ_CREATE_DPI, SJ_DPI_VPTR, dpi_vtable_cells; auto|].
      split; [exact SJS7|]. split; [eassumption|]. split; [eassumption|]. split; [unfold p48_cells; eassumption|].
      split. { exists (Z_to_bv 64 13). split; [unfold res_cells; cbn [bv_eqb Z_to_bv]; eassumption|]. left. rewrite unsigned_lit by lia. lia. }
      split; [do 13 eexists; (split; [unfold impl_cells16; eassumption| reflexivity])|].
      subst tcap scap. split; [exact BRTP| exact BRSB].
  Qed.
End Proofs.
End WithCeiling0.
