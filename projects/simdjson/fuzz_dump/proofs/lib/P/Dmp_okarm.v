(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel DrtModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Pj_loc_defs Pj_loc_get Pj_os_defs Pj_os_ctor Pj_os_dtor.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_stage2_iface El_defs El_os_defs El_ins_iface Dmp_defs Dmp_pj_iface Dmp_lftoi.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma implM_free_nulls : forall {A} (k : M PState A) s Q ms,
  implM psegs k s Q ms -> implM psegs (mbind (drt_free_nulls lops) (fun _ => k)) s Q ms.
Proof. intros A k s Q ms H. exact H. Qed.

Definition os_ctor_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo OS : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 672, q); (OS, OS + 288); (PJ_LOC_LO, PJ_LOC_HI)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo q /\ OSFRESH m' OS /\ LOCB m'.
Lemma os_ctor_callZ : forall ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (q lo OS : Z) (canary : word) (junk : list byte),
  stk psegs m lo q -> lo <= q - 672 -> GLOBALS_TOP <= lo -> q < 2^62 ->
  pj_locale m -> rw_cells psegs m OS [CB 288 junk] -> q <= OS -> OS + 288 < 2^62 -> pj_consts m -> ssp_cells m canary ->
  rw_cells psegs m RNEED_LOCKS [C1 (Z_to_bv 8 0)] -> mem_inv psegs m ->
  evt psegs (os_ctor_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_OSCTOR) fc None m (seg_rom psegs)).
Proof.
  intros until junk. intros ST LO GLO Q62 LOC OSC QOS OS62 (_ & _ & GOTV & _ & LCK & _) (SSP1 & SSP2) NL MI.
  assert (Q0 : 0 <= q) by (destruct ST as [L0 _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  unfold got_ssp, ssp_guard in SSP1, SSP2. unfold RNEED_LOCKS in NL. unfold MallocRep.wz in GOTV, LCK. unfold GLOBALS_TOP in GLO.
  eapply evt_mono.
  - eapply (os_ctor_proof ra (Z_to_bv 64 q)) with (lo := lo) (OS := OS) (canary := canary) (junk := junk); rewrite ?U; try assumption.
  - intros ms' P. unfold os_ctor_post in P. rewrite U in P. exact P.
Qed.

Definition ios_dtor_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS fill : Z) (j148 j284 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 48, q); (OS + 136, OS + 144)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo q
    /\ rw_cells psegs m' (OS + 136) (ios_cells OS 0xca720 fill j148 j284).
Lemma ios_dtor_callZ : forall ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo OS fill : Z) (j148 j284 : list byte),
  stk psegs m lo q -> lo <= q - 48 -> GLOBALS_TOP <= lo ->
  rw_cells psegs m (OS + 136) (ios_cells OS 0xc7330 fill j148 j284) -> q <= OS -> OS + 288 < 2^62 ->
  mem_inv psegs m ->
  evt psegs (ios_dtor_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS fill j148 j284 m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 136)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x73034) fc None m (seg_rom psegs)).
Proof.
  intros until j284. intros ST LO GLO IOC QOS OS62 MI.
  assert (Q0 : 0 <= q) by (destruct ST as [L0 _]; lia).
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia). unfold GLOBALS_TOP in GLO.
  eapply evt_mono.
  - eapply (ios_dtor_proof ra (Z_to_bv 64 q)) with (lo := lo) (OS := OS) (fill := fill) (j148 := j148) (j284 := j284); rewrite ?U; try assumption.
  - intros ms' P. unfold ios_dtor_post in P. rewrite U in P. exact P.
Qed.

Lemma lb_below : forall s LB m a, RHEAP s LB m -> in_block LB a -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x101000 <= a).
Proof.
  intros s LB m a H (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ H Hb) as (R1 & R2 & R3 & R4 & R5).
  unfold OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec.Malloc.MCEIL in R4. lia.
Qed.

Lemma okarm_client_out : forall s LBall m q0 lo a (W : list (Z * Z)),
  RHEAP s LBall m -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q0 - 400 ->
  (forall x, outside W x \/ (lo <= x < q0 - 400) \/ (q0 - 400 <= x < q0 - 112) \/ (PJ_LOC_LO <= x < PJ_LOC_HI) \/ (EL_TPLOC <= x < EL_TPLOC + 8) \/ (LX_ERRNO <= x < LX_ERRNO + 4)) ->
  0 <= a < 2^64 -> lx_client LBall (q0 + -400) (dmp_okarm_X q0) a -> outside W a.
Proof.
  intros s LBall m q0 lo a W HEAP CEIL GLO LO HW Ha [NX HC].
  destruct (HW a) as [H|H]; [exact H| exfalso].
  unfold dmp_okarm_X, LXW_SJ, LXW_TP, SJ_STATICS_LO, SJ_STATICS_HI in NX. cbn [rin_ivs fst snd] in NX.
  unfold GLOBALS_TOP in *. rewrite ELX in H.
  destruct HC as [HC|[HC|[HC NRS]]]; [lia| pose proof (lb_below _ _ _ _ HEAP HC); lia|].
  unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in NRS. lia.
Qed.

Lemma okarm_tail : forall {A} (k : M PState A) (Q : A -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 u0 u1 a0 a1 a2 a3 a4 a5 a6 a7 u18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m00 m : mem) (s00 s : PState) (LBall : list block) (q0 lo B : Z) (errv : word),
  (forall s' ms', dmp_okarm_post q0 gp s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LBall lo B m00 s' ms' -> implM psegs k s' Q ms') ->
  frm0 fc -> mem_inv psegs m -> stk psegs m lo (q0 + -400) -> rw_cells psegs m LX_ERRNO [C4 errv] -> rauxv_ok m B ->
  ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 -> RHEAP s LBall m -> lx_pres LBall (q0 + -400) (dmp_okarm_X q0) m00 m ->
  rw_cells psegs m SJ_STATICS_LO (sj_cells true) -> LOCB m -> el_extra m -> rw_cells psegs m EL_TPLOC [C8 (MallocRep.wz EL_GLOC)] ->
  (exists (pb pp ep : word) (fill : Z) (dum j148 j284 : list byte), rw_cells psegs m (q0 + -400) (os_cells (q0 + -400) pb pp ep fill dum j148 j284)) ->
  pj_consts m ->
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q0 - 400 - 48 -> q0 <= B -> q0 < 2^62 ->
  implM psegs k s Q (MS (mkR x1 (Z_to_bv 64 (q0 + -400)) gp (Z_to_bv 64 RATP) t0 t1 t2 u0 u1 a0 a1 a2 a3 a4 a5 a6 a7 u18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x3a7f8) fc None m (seg_rom psegs)).
Proof.
  intros until errv. intros KPOST FRM MI ST ERR AUX FA SO HEAP PRES IMPC LB EX TPC OSU PJC CEIL GLO LO QB Q62.
  rewrite ELX in ERR. unfold GLOBALS_TOP in GLO.
  unfold SJ_STATICS_LO in IMPC. cbn [sj_cells] in IMPC.
  destruct LB as (lj1 & lj2 & lj3 & lj4 & lj5 & lj6 & LBC). unfold locb_cells in LBC.
  destruct OSU as (pb & pp & ep & fill & dum & j148 & j284 & OSC). unfold os_cells, sb_cells, ios_cells in OSC. cbn [app] in OSC.
  pose proof PJC as (_ & _ & GOTV & _). unfold MallocRep.wz in GOTV.
  pose proof (munch_refl [(q0 - 448, q0 - 400); (q0 - 400, q0 - 256)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold implM. iprefix.

  step. step. step. step. step. step.

  step. step. step. step. fix_lit_store.

  step. step. step. step. step. step. if_true. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with H : rw_cells _ mx (q0 + -400) _ |- _ => rename H into OSC1 end end.
  destruct (rw_cells_split_at _ _ _ 10%nat OSC1) as [OSL IOS]. cbn [firstn skipn cells_size csize Nat.add] in OSL, IOS. clear OSC1.

  step. step. replace (Z_to_bv 64 (q0 + -264)) with (Z_to_bv 64 (q0 + -400 + 136)) by (f_equal; lia).
  call ios_dtor_callZ; [exact ST| lia| unfold GLOBALS_TOP; lia| exact IOS| lia| lia| assumption|].
  rename PC into ST5. lazymatch goal with H : rw_cells _ _ (q0 + -400 + 136) _ |- _ => rename H into IOSC end.
  unfold ios_cells in IOSC.
  pose proof (rw_cells_join _ _ _ _ _ OSL IOSC ltac:(cbn [cells_size csize Nat.add]; lia)) as OSJ.
  apply rw_cells_forget in OSJ. destruct OSJ as [bsO OSJ]. cbn [app cells_size csize Nat.add] in OSJ. clear OSL IOSC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  apply evt_done. to_implM. eapply KPOST. unfold dmp_okarm_post. do 23 eexists.
  split; [unfold DMP_JOIN; cbv delta [mkR]; reflexivity|].
  split; [exact FRM|]. split; [exact MI0|]. split; [exact ST5|]. split; [eassumption|].
  split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
  split; [exact FA|]. split; [exact SO|].
  split. { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
  split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
           intros a Ha HCL. eapply (okarm_client_out _ _ _ q0 _ _ _ HEAP CEIL); [unfold GLOBALS_TOP; lia| lia| | exact Ha| exact HCL]. intros xx. cbn [outside]. lia. }
  split. { split; [| split; [right|]].
           - first [exact IMPC| eapply rw_cells_agree; [exact AG| exact IMPC|]; intros a Ha; cbn in Ha; cbn [outside]; lia].
           - eapply LOCB_transport; [exists lj1, lj2, lj3, lj4, lj5, lj6; exact LBC| exact MU| exact WM|]. cbv [disjoint_from fst snd]. repeat split; lia.
           - eapply el_extra_munch; [exact MU| exact WM| | exact EX]. intros a Ha. cbn [outside]. lia. }
  split. { first [exact TPC| eapply rw_cells_agree; [exact AG| exact TPC|]; intros a Ha; cbn in Ha; cbn [outside]; lia]. }
  exists bsO; exact OSJ.
Qed.

Section Proofs.
  Hypothesis PJ : pj_root_stmt.

  Theorem dmp_okarm_proof : dmp_okarm_stmt.
  Proof.
    unfold dmp_okarm_stmt. intros until jgap.
    intros HEAP INT INS AUX QB B62 ST CEIL GLO LO ERR MI FRM AL16 Q400 LXS SJS SSP LEN CAP SRET GAP DOCC OKR KPOST.
    unfold DMP_OKARM_STACK, DMP_OKARM in *. unfold GLOBALS_TOP in GLO.
    assert (Q62 : q0 < 2^62) by (clear - QB B62; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec.Malloc.MCEIL in CEIL'.
    assert (AL0 : (q0 + -400) mod 16 = 0) by (clear - AL16; replace (q0 + -400) with (q0 + (-25) * 16) by lia; rewrite Z.mod_add by lia; exact AL16).
    pose proof (lx_statics_pj _ LXS) as PJC. pose proof (lx_statics_el _ LXS) as (_ & _ & _ & TPC).
    pose proof (el_dcc_of_consts m PJC) as DCC. pose proof (dmp_dcc_of_consts m PJC) as DCB.
    destruct DCC as (DC1 & DC2 & DC3 & DC4 & DC5 & DC6). unfold dmp_dcc, DMP_NPB_SLOT, DMP_NP_BOOL in DCB.
    pose proof (RHEAP_need_locks _ _ _ HEAP) as NLK.
    pose proof (sj_statics_locale _ _ SJS) as LOC. pose proof (sj_statics_impl _ _ SJS) as IMPC. pose proof (sj_statics_extra _ _ SJS) as EX.
    unfold SJ_STATICS_LO in IMPC. cbn [sj_cells] in IMPC.
    rewrite ELX in ERR.

    destruct OKR as [KO|(_ & tws & sbs & TB & SBB & WF & FAB & TL & SL)]; [exfalso; rewrite unsigned_lit in KO by lia; lia|].
    pose proof (tape_wfS_wf _ _ _ _ _ WF) as WF'.
    destruct (rw_cells_split_at _ _ _ 2%nat DOCC) as [DOC2 _]. cbn [firstn skipn cells_size csize Nat.add] in DOC2.
    pose proof (LH_block_range _ _ _ _ HEAP INT) as (TR0 & TRA & _ & TRC & TRI). cbn [blk_addr blk_size fst snd] in TR0, TRA, TRC, TRI.
    pose proof (LH_block_range _ _ _ _ HEAP INS) as (SR0 & _ & _ & SRC & SRI). cbn [blk_addr blk_size fst snd] in SR0, SRC, SRI.
    unfold OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec.Malloc.MCEIL in TRC, SRC.
    assert (RU3 : 0 <= roundup64 (cap + 3)) by (unfold roundup64; lia).
    assert (RU5 : 0 <= roundup64 (5 * (cap / 3) + 64)) by (unfold roundup64; lia).

    apply implM_free_nulls.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix.

    step. step. step.

    pose proof (rw_cells_join _ _ _ _ _ SRET GAP ltac:(cbn [cells_size csize Nat.add]; lia)) as OSA. cbn [app] in OSA.
    destruct (rw_cells_forget _ _ _ _ OSA) as [jO OSJ]. cbn [cells_size csize Nat.add] in OSJ. clear OSA SRET GAP.
    step.
    eapply evt_cut.
    { eapply (os_ctor_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (q0 + -400) lo (q0 + -400) canary jO);
        [exact ST| lia| unfold GLOBALS_TOP; lia| lia| exact LOC| exact OSJ| lia| lia| exact PJC| exact SSP| exact NLK| exact MI]. }
    cbv beta. intros ms1 PO. unfold os_ctor_postZ in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & OSF1 & LB1).
    replace (ret_pc (Z_to_bv 64 0x3a7e4)) with (Z_to_bv 64 0x3a7e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
    Ltac tr1 AG H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    tr1 AG1 DOC2. tr1 AG1 ERR. tr1 AG1 TPC. tr1 AG1 IMPC.
    tr1 AG1 DC1. tr1 AG1 DC2. tr1 AG1 DC3. tr1 AG1 DC4. tr1 AG1 DC5. tr1 AG1 DC6. tr1 AG1 DCB.
    apply (bytes_at_agree _ _ _ _ _ AG1) in TB;
      [| rewrite u64s_length, length_map; intros a Ha; rewrite Nat2Z.inj_mul in Ha; cbn [outside]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; clear - Ha TR0 TRC TRI TL CEIL LO RU3; lia].
    apply (bytes_at_agree _ _ _ _ _ AG1) in SBB;
      [| rewrite length_map; intros a Ha; cbn [outside]; clear - Ha SR0 SRC SRI SL CEIL LO RU5; lia].
    apply (pj_consts_agree _ _ _ AG1) in PJC; [| intros a Ha; cbn [outside]; lia].
    apply (ssp_cells_agree _ _ _ _ AG1) in SSP; [| intros a Ha; unfold ssp_addr, got_ssp, ssp_guard in Ha; cbn [outside]; lia].
    assert (EX1 : el_extra m1) by (eapply el_extra_munch; [exact MU1| exact WM1| | exact EX]; intros a Ha; cbn [outside]; lia).
    assert (HEAP1 : RHEAP s LBall m1).
    { eapply LH_frame; [exact HEAP| exact MU1| exact WM1|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
    assert (PRES1 : lx_pres LBall (q0 + -400) (dmp_okarm_X q0) m m1).
    { eapply lx_pres_of_munch; [exact MU1| exact WM1|].
      intros a Ha HCL. eapply (okarm_client_out _ _ _ q0 _ _ _ HEAP CEIL); [unfold GLOBALS_TOP; lia| lia| | exact Ha| exact HCL]. intros xx. cbn [outside]. lia. }
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl psegs m1) as WM.

    step. step. step. step. step.
    replace (Z_to_bv 64 (q0 + -272)) with (Z_to_bv 64 (q0 + -400 + 128)) by (f_equal; lia).
    eapply evt_cut.
    { unfold pj_root_stmt in PJ.
      eapply (PJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (q0 + -400) lo (q0 + -400) (q0 + -88) TAPE SBUF tws sbs canary errv);
        [ exact WF'| exact FAB| exact DOC2| lia| right; lia| lia
        | exact TB| lia| apply mod8_of_mod16; exact TRA| clear - TRC TL CEIL RU3; lia| clear - TRI TL RU3; unfold GLOBALS_TOP; lia
        | exact SBB| lia| clear - SRC SL CEIL RU5; lia| clear - SRI SL RU5; unfold GLOBALS_TOP; lia
        | exact OSF1| lia| lia| exact LB1| (split; [exact DC1| split; [exact DC2| split; [exact DC3| split; [exact DC4| split; [exact DC5| exact DC6]]]]])| exact DCB
        | exact SSP| exact TPC| rewrite ELX; exact ERR
        | exact ST1| unfold pj_need, DMP_PJ_FRAME, DMP_PJ_LEAF; change (Z.of_nat TAPE_MAX_DEPTH) with 1024%Z; lia| unfold GLOBALS_TOP; lia| exact AL0| exact MI1| exact FRM ]. }
    cbv beta. intros ms2 PO. unfold pj_post in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & FRM2 & MU2 & WM2 & MI2 & ST2
                     & OSX2 & TPC2 & (errv2 & ERR2) & SSP2 & LB2).
    assert (OSC2 : exists (pb pp ep : word) (fill : Z) (dum j148 j284 : list byte), rw_cells psegs m2 (q0 + -400) (os_cells (q0 + -400) pb pp ep fill dum j148 j284)).
    { destruct OSX2 as (pb & pp & ep & fill & dum & j148 & j284 & OSC & _ & _). exists pb, (Z_to_bv 64 pp), (Z_to_bv 64 ep), fill, dum, j148, j284.
      rewrite os_cells_X. exact OSC. }
    replace (ret_pc (Z_to_bv 64 0x3a7f8)) with (Z_to_bv 64 0x3a7f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
    apply (pj_consts_agree _ _ _ AG2) in PJC; [| intros a Ha; unfold pj_W; rewrite ELX; cbn [outside]; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in IMPC; [| intros a Ha; cbn in Ha; unfold pj_W; rewrite ELX; cbn [outside]; lia].
    assert (EX2 : el_extra m2) by (eapply el_extra_munch; [exact MU2| exact WM2| | exact EX1]; intros a Ha; unfold pj_W; rewrite ELX; cbn [outside]; lia).
    assert (HEAP2 : RHEAP s LBall m2).
    { eapply LH_frame; [exact HEAP1| exact MU2| exact WM2|]. unfold pj_W. rewrite ELX.
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. unfold pj_W, RAUXV_CELL. rewrite ELX. repeat constructor; cbn; lia. }
    assert (PRES2 : lx_pres LBall (q0 + -400) (dmp_okarm_X q0) m m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU2| exact WM2|].
      intros a Ha HCL. eapply (okarm_client_out _ _ _ q0 _ _ _ HEAP CEIL); [unfold GLOBALS_TOP; lia| lia| | exact Ha| exact HCL].
      intros xx. unfold pj_W. rewrite ELX. cbn [outside]. lia. }
    rewrite ELX in ERR2.
    ihere. to_implM.
    eapply okarm_tail with (m00 := m) (s00 := s);
      [exact KPOST| exact FRM2| exact MI2| exact ST2| rewrite ELX; exact ERR2| exact AUX2| reflexivity| reflexivity| exact HEAP2| exact PRES2
      | exact IMPC| exact LB2| exact EX2| exact TPC2| exact OSC2| exact PJC| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact QB| exact Q62].
  Qed.
End Proofs.
End WithCeiling0.
