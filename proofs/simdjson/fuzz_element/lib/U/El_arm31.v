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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Pj_loc_defs Pj_loc_get Pj_os_defs Pj_os_ctor Pj_os_dtor.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Atp_pid Atp_defs Atp_h_defs El_defs El_hdr El_h2 El_h3 El_act El_dump_iface El_osd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma implM_free_nulls : forall {A} (k : unit -> M PState A) s Q ms,
  implM usegs (k tt) s Q ms -> implM usegs (mbind (el_free_nulls lops) k) s Q ms.
Proof. intros A k s Q ms H. exact H. Qed.

Definition os_ctor_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo OS : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 672, q); (OS, OS + 288); (0xeddc8, 0xeec78)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ OSFRESH m' OS /\ LOCB m'.
Lemma os_ctor_callZ : forall ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (q lo OS : Z) (canary : word) (junk : list byte),
  stk usegs m lo q -> lo <= q - 672 -> 0x111000 <= lo -> q < 2^62 ->
  pj_locale m -> rw_cells usegs m OS [CB 288 junk] -> q <= OS -> OS + 288 < 2^62 -> pj_consts m -> ssp_cells m canary ->
  rw_cells usegs m RNEED_LOCKS [C1 (Z_to_bv 8 0)] -> mem_inv usegs m ->
  evt usegs (os_ctor_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_OSCTOR) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros ST LO GLO Q62 LOC OSC QOS OS62 (_ & _ & GOTV & _ & LCK & _) (SSP1 & SSP2) NL MI.
  assert (Q0 : 0 <= q) by (destruct ST as [L0 _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  unfold got_ssp, ssp_guard in SSP1, SSP2. unfold RNEED_LOCKS in NL. unfold MallocRep.wz in GOTV, LCK.
  eapply evt_mono.
  - eapply (os_ctor_proof ra (Z_to_bv 64 q)) with (lo := lo) (OS := OS) (canary := canary) (junk := junk); rewrite ?U; try assumption.
  - intros ms' P. unfold os_ctor_post in P. rewrite U in P. exact P.
Qed.

Definition arm31_W (lo sp0 : Z) : list (Z * Z) :=
  [(lo, sp0); (sp0 + 8, sp0 + 296); (0xeddc8, 0xeec78); (EL_TPLOC, EL_TPLOC + 8); (LX_ERRNO, LX_ERRNO + 4)].

Section Proofs.
  Hypothesis DUMP : dump_stmt.

  Theorem arm31_proof : arm_stmt 31 0x3c444.
  Proof.
    unfold arm_stmt. intros until p50. intros EA AE HK.
    pose proof AE as AE'.
    destruct AE' as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                     & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity.
    assert (AL0 : sp0 mod 16 = 0) by (clear - AL16; replace sp0 with (sp0 + 528 + (-33) * 16) by lia; rewrite Z.mod_add by lia; exact AL16).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 _ _ _ [_ T8]].
    pose proof (aenv_ranges E st m OK HEAP) as (TR & SR & _).
    pose proof (el_root_elem E OK) as [_ NR].
    pose proof AI as (TAPEB & SBUFB & PTRB & DOCC). rewrite EDOC in DOCC.

    assert (LXS : lx_statics m).
    { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
      pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      unfold LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
    pose proof (lx_statics_pj _ LXS) as PJC. pose proof (lx_statics_el _ LXS) as (_ & _ & _ & TPC).
    pose proof (sj_statics_locale _ _ SJS) as LOC. pose proof (RHEAP_ssp _ _ _ HEAP) as SSP. pose proof (RHEAP_need_locks _ _ _ HEAP) as NLK.

    unfold el_act, el_throwing. rewrite EA. cbn [Z.eqb Pos.eqb orb]. apply implM_free_nulls.

    pose proof (rw_cells_join _ _ _ _ _ RES OS ltac:(cbn [cells_size csize Nat.add]; lia)) as OSA. cbn [app] in OSA.
    destruct (rw_cells_forget _ _ _ _ OSA) as [jO OSJ]. cbn [cells_size csize Nat.add] in OSJ. clear OSA.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.

    step. step.
    eapply evt_cut.
    { eapply (os_ctor_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m sp0 lo (sp0 + 8) rr_guard jO);
        [exact ST| lia| lia| lia| exact LOC| exact OSJ| lia| lia| exact PJC| exact SSP| exact NLK| exact MI]. }
    cbv beta. intros ms1 PO. unfold os_ctor_postZ in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & OSF1 & LB1).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
    assert (BLA : forall a, in_block (ae_LB E) a -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x111000 <= a)).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (R0 & _ & _ & RC & RI). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RC. lia. }
    Ltac tr1 AG H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    tr1 AG1 ROOT. tr1 AG1 DOCC. rewrite ELX in ERR. tr1 AG1 ERR. tr1 AG1 TPC.
    assert (TBL : forall a, ae_TAPE E <= a < ae_TAPE E + 8 * Z.of_nat (length (ae_tws E)) -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x111000 <= a))
      by (intros a Ha; apply BLA; eapply in_blocks_in_block; [exact BT| exact Ha]).
    assert (SBL : forall a, ae_SBUF E <= a < ae_SBUF E + Z.of_nat (length (ae_sbs E)) -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x111000 <= a))
      by (intros a Ha; apply BLA; eapply in_blocks_in_block; [exact BS| exact Ha]).
    apply (bytes_at_agree _ _ _ _ _ AG1) in TAPEB;
      [| rewrite u64s_length, length_map; intros a Ha; rewrite Nat2Z.inj_mul in Ha; specialize (TBL a ltac:(clear - Ha; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; lia)); cbn [outside]; clear - Ha TBL CEIL LO; lia].
    apply (bytes_at_agree _ _ _ _ _ AG1) in SBUFB;
      [| rewrite length_map; intros a Ha; specialize (SBL a Ha); cbn [outside]; clear - Ha SBL CEIL LO; lia].
    apply (pj_consts_agree _ _ _ AG1) in PJC; [| intros a Ha; cbn [outside]; lia].
    apply (ssp_cells_agree _ _ _ _ AG1) in SSP; [| intros a Ha; unfold ssp_addr, got_ssp, ssp_guard in Ha; cbn [outside]; lia].
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.

    unfold el_root in ROOT. assert (DOCPOS : 0 < ae_DOC E) by lia.
    assert (DOC8 : Z.land (ae_DOC E) 7 = 0).
    { pose proof (Z.div_mod sp0 16 ltac:(lia)) as DM. rewrite AL0, Z.add_0_r in DM.
      rewrite EDOC. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
      apply Z.mod_divide; [lia|]. exists (2 * (sp0 / 16) + 42). lia. }
    Ltac to_dump :=
      lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let K := fresh "K" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K; to_dump]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
          let b := eval vm_compute in (Z.eqb p EL_DUMP) in
          lazymatch b with true => idtac | false => step; to_dump end
      end.
    to_dump.
    replace (Z_to_bv 64 (sp0 + 136)) with (Z_to_bv 64 (sp0 + 8 + 128)) by (f_equal; lia).
    eapply evt_cut.
    { eapply (DUMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 sp0 lo (sp0 + 8) (ae_DOC E) (ae_TAPE E) (ae_SBUF E) (ae_tws E) (ae_sbs E) rr_guard errv);
        [ exact WF| exact SBS| rewrite EDOC; exact DOCC| rewrite EDOC; lia| rewrite EDOC; right; lia| rewrite EDOC; lia
        | exact TAPEB| lia| exact T8| lia
        | exact (in_blocks_image _ _ _ _ _ HEAP BT ltac:(lia))
        | exact SBUFB| lia| lia
        | exact (in_blocks_image _ _ _ _ _ HEAP BS ltac:(lia))
        | exact OSF1| lia| lia| clear - AL0; rewrite (Z.div_mod sp0 16) by lia; rewrite AL0, Z.add_0_r; replace (16 * (sp0 / 16) + 8) with (1 * 8 + (2 * (sp0 / 16)) * 8) by lia; rewrite Z_mod_plus_full; reflexivity
        | exact LB1| exact PJC| exact SSP| exact TPC| rewrite ELX; exact ERR
        | exact ST1| unfold EL_DUMP_STACK; lia| unfold GLOBALS_TOP; lia| exact AL0| exact MI1| exact FRM ]. }
    cbv beta. intros ms2 PO. unfold dump_post in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & FRM2 & MU2 & WM2 & MI2 & ST2
                     & (pb & pp & ep & fill & dum & j148 & j284 & OSC2) & TPC2 & (errv2 & ERR2) & LB2).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
    apply (pj_consts_agree _ _ _ AG2) in PJC; [| intros a Ha; unfold dump_W, EL_DUMP_STACK; rewrite ELX; cbn [outside]; lia].
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.

    step. step.
    pose proof PJC as (_ & _ & GOTV & _).
    eapply evt_cut.
    { eapply (osd_spec ios_dtor_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 sp0 lo (sp0 + 8));
        [exact ST2| lia| unfold GLOBALS_TOP; lia| lia| lia| exact OSC2| exact GOTV| exact MI2]. }
    cbv beta. intros ms3 PO. unfold osd_post in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & (jk & OSJ3)).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

    assert (MUA : munch (arm31_W lo sp0) m m3).
    { unfold arm31_W. eapply munch_trans; [| eapply munch_trans]; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]];
        unfold sub_fp, dump_W, EL_DUMP_STACK; rewrite ?ELX; cbn [outside]; intros x Hx; lia. }
    assert (WMA : wmono usegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
    pose proof (agree_on_of_munch _ _ _ MUA WMA) as AG.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.

    step.
    ihere. apply HK. unfold EL_EXIT in *.

    assert (FRH : forall a, (sp0 <= a < sp0 + 8 \/ sp0 + 296 <= a < sp0 + 528) -> outside (arm31_W lo sp0) a).
    { intros a Ha. unfold arm31_W. rewrite ELX. cbn [outside]. lia. }
    assert (INB : forall b a, In b (ae_LB E) -> blk_addr b <= a < blk_addr b + blk_size b -> outside (arm31_W lo sp0) a).
    { intros b a Hb Ha. assert (IB : in_block (ae_LB E) a) by (exists b; auto). specialize (BLA a IB). unfold arm31_W. rewrite ELX. cbn [outside]. lia. }
    assert (LBsub : forall b, In b LB -> In b (ae_LB E)) by (intros b Hb; rewrite ELB; unfold el_blocks; do 7 right; exact Hb).
    Ltac trA AG FRH H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; try unfold p48_cells in Ha; cbn in Ha; apply FRH; lia].
    trA AG FRH J0. trA AG FRH PA0. trA AG FRH PIMPL. trA AG FRH PA16. trA AG FRH DCAP. trA AG FRH P48. trA AG FRH XSEL. trA AG FRH XFD. trA AG FRH SAVE.
    lazymatch goal with H : rw_cells usegs m1 (sp0 + 296) _ |- _ => rename H into ROOT1 end.
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU2 WM2)) in ROOT1; [| intros a Ha; cbn in Ha; unfold dump_W, EL_DUMP_STACK; rewrite ELX; cbn [outside]; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU3 WM3)) in ROOT1; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    pose proof AI as (_ & _ & _ & DOCC0). rewrite EDOC in DOCC0. trA AG FRH DOCC0.
    apply (rw_cells_agree _ _ _ _ _ AG) in THIS; [| intros a Ha; eapply INB; [rewrite ELB; unfold el_blocks; do 3 right; left; reflexivity| unfold impl_cells16 in Ha; cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]].
    destruct VR as (ELS & SZ & SV & BLK). trA AG FRH SV.
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK; [| intros a _ Ha; eapply INB; [rewrite ELB; unfold el_blocks; do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].

    pose proof (rw_cells_join _ _ _ _ _ J0 OSJ3 ltac:(cbn [cells_size csize Nat.add]; lia)) as Q1.
    pose proof (rw_cells_join _ _ _ _ _ Q1 ROOT1 ltac:(cbn [app cells_size csize Nat.add]; lia)) as Q2. cbn [app] in Q2.
    destruct (rw_cells_forget _ _ _ _ Q2) as [jlo LOW]. cbn [cells_size csize Nat.add] in LOW.
    destruct (rw_cells_forget _ _ _ _ XSEL) as [jsel XSEL']. cbn [cells_size csize Nat.add] in XSEL'.
    pose proof (rw_cells_join _ _ _ _ _ XSEL' XFD ltac:(cbn [cells_size csize Nat.add]; lia)) as Q5. cbn [app] in Q5.
    destruct (rw_cells_forget _ _ _ _ Q5) as [jmid MID]. cbn [cells_size csize Nat.add] in MID.
    pose proof (rw_cells_join _ _ _ _ _ DOCC0 DCAP ltac:(cbn [cells_size csize Nat.add]; lia)) as DOC3. cbn [app] in DOC3.

    assert (HEAP3 : RHEAP st (ae_LB E) m3).
    { eapply LH_frame; [exact HEAP| exact MUA| exact WMA|]. unfold arm31_W. rewrite ELX.
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MUA| exact WMA|]. unfold arm31_W, RAUXV_CELL. rewrite ELX. repeat constructor; cbn; lia. }
    assert (PRES3 : lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW; LXW_TP] m0 m3).
    { eapply lx_pres_trans; [apply pres_X3; exact PRES|]. eapply lx_pres_of_munch; [exact MUA| exact WMA|].
      intros a Ha [NX HC]. unfold LXW_SJ, LXW_UNW, LXW_TP, SJ_STATICS_LO, SJ_STATICS_HI in NX. cbn [rin_ivs fst snd] in NX. unfold arm31_W. rewrite ELX. cbn [outside].
      assert (BLB : in_block LB a -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x111000 <= a)).
      { intros (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (R0 & _ & _ & RC & RI). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in RC. lia. }
      destruct HC as [HC|[HC|[HC NRS]]]; [clear - HC LO CEIL NX; lia| specialize (BLB HC); clear - BLB LO CEIL GLO NX; lia|].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in NRS. clear - HC NRS NX LO GLO CEIL. lia. }
    assert (LB3 : LOCB m3) by (eapply LOCB_transport; [exact LB2| exact MU3| exact WM3|]; cbv [disjoint_from fst snd]; repeat split; lia).
    assert (SJS3 : sj_statics m3 true).
    { destruct SJS as (SC & _ & EX). split; [| split; [right; exact LB3|]].
      - eapply rw_cells_agree; [exact AG| exact SC|]. intros a Ha. cbn in Ha. unfold SJ_STATICS_LO in Ha. unfold arm31_W. rewrite ELX. cbn [outside]. clear - Ha LO GLO. lia.
      - eapply el_extra_munch; [exact MUA| exact WMA| | exact EX]. intros a Ha. unfold arm31_W. rewrite ELX. cbn [outside]. clear - Ha LO GLO. lia. }
    assert (PL3 : payload_ok m3 LB D d).
    { eapply payload_ok_agree; [exact AG| exact PL|]. intros b a Hb Ha. eapply INB; [apply LBsub; exact Hb| exact Ha]. }
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU3 WM3)) in TPC2; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    rewrite ELX in ERR2. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU3 WM3)) in ERR2; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    unfold act_post. do 25 eexists. exists F2, fc2, m3, errv2, true. exists nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50, j313, j329, j361, jlo, jmid.
    split; [reflexivity|].
    split; [exact HEAP3|]. split; [exact AUX3|]. split; [exact MI3|]. split; [exact ST3|]. split; [rewrite ELX; exact ERR2|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FRM2|].
    split; [exact PRES3|]. split; [exact TPC2|]. split; [exact SJS3|]. split; [exact PL3|].
    split; [exact LOW|]. repeat (split; [assumption|]). exact SAVE.
  Qed.
End Proofs.
End WithCeiling0.
