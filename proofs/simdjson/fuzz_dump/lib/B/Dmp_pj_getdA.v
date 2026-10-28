From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Mem Frame Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit
     El_os_defsA Pj_defsA Pj_ser_trefA Atp_defsA Atp_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition DMP_PJ_GETD_A : Z := 0xb01f0.

Lemma shz_munch : forall W (m m' : mem) a n, shz m a n -> munch W m m' ->
  (forall x, a <= x < a + n -> outside W (x / 8 + 2147450880)) -> 0 <= a -> a + n <= 2^47 -> shz m' a n.
Proof.
  intros W m m' a n H MU HW A0 AH x Hx. pose proof (H x Hx) as R.
  rewrite ov_rdn in R |- *. cbn [rdn] in R |- *. unfold mrd in R |- *.
  rewrite (MU (wa (x / 8 + 2147450880))); [exact R|].
  rewrite wa_unsigned by (Z.div_mod_to_equations; lia). apply HW. exact Hx.
Qed.

Lemma tix_cpsB : forall (E : aenvA) (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (sp i RA : Z)
    (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  aenvA_ok E -> AINV_A E m -> client_consts m -> 0 <= i < ae_n E ->
  stk bsegs m (ae_lo E) sp -> ae_lo E + 16 <= sp -> sp <= USTACK_TOP -> mem_inv bsegs m ->
  0 <= RA < 2^64 -> RA mod 2 = 0 ->
  (forall (m' : mem) (xa1 xa3 xa4 : word), munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) sp ->
     evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz (ae_TAPE E + 8 * i)) xa1 (wz (ae_TAPE E)) xa3 xa4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA) fc None m' (seg_rom bsegs))) ->
  evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz (ae_DOC E)) (wz i) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PJ_TREF_A) fc None m (seg_rom bsegs)).
Proof.
  intros until t6. intros OK AI CC IR ST LO HI MI RA0 RA2 HK.
  pose proof OK as OK'. destruct OK' as [_ _ _ _ (T16 & NT8 & TN & T0 & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP, SEGTOP_A in *.
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  pose proof AI as (TB & SB & PB & DC & DSH).
  change [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] with ([C8 (Z_to_bv 64 (ae_TAPE E))] ++ [C8 (Z_to_bv 64 (ae_SBUF E))]) in DC.
  apply rw_cells_app in DC. destruct DC as [DC _].
  eapply evt_cut.
  { eapply (tref_walk (ae_DOC E) (ae_TAPE E) i sp (ae_lo E)); [exact ST| lia| lia| lia| exact CC| lia| lia| lia
      | unfold shad, SHB in *; exact DSH| exact DC| lia| clear - T16; Z.div_mod_to_equations; lia| lia| lia| lia| exact MI]. }
  cbv beta. intros ms' (m' & a4' & -> & MU & WM & MI' & ST').
  rewrite (ret_pc_even RA) by lia.
  replace (sp - 16) with (sp + -16) in MU by lia.
  exact (HK m' (wz 0) (wz (2^60)) a4' MU WM MI' ST').
Qed.

Lemma getd_walk : forall (E : aenvA) (sp EL i : Z)
    (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  aenvA_ok E -> AINV_A E m -> client_consts m -> mem_inv bsegs m ->
  stk bsegs m (ae_lo E) sp -> ae_lo E + 64 <= sp -> sp <= USTACK_TOP -> sp mod 16 = 0 ->
  shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells bsegs m EL [C8 (wz (ae_DOC E)); C8 (wz i)] -> EL mod 8 = 0 -> shz m EL 16 ->
  (EL + 16 <= sp - 64 \/ sp <= EL) -> 0 < EL -> EL + 16 <= USTACK_TOP ->
  0 <= i -> i + 1 < ae_n E -> ae_T E i = tword t_dbl 0 ->
  evt bsegs (fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms = MS (mkR ra (wz sp) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              (bvmap_set 10 (wz (ae_T E (i + 1))) F) (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 64, sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' (ae_lo E) sp /\ AINV_A E m')
    (MS (mkR ra (wz sp) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz EL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz DMP_PJ_GETD_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK AI CC MI ST LO HI Q16 SZT0 NODE N8 SZN0 NQ N0 NH I0 IN TI.
  change TPV_A with TPV. unfold DMP_PJ_GETD_A.
  lazymatch goal with |- evt _ ?P _ => set (POST := P) end.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
  unfold SEGTOP_A, USTACK_TOP in *.
  assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TI; unfold tword, t_dbl; lia).
  assert (AIW : forall m', munch [(sp - 64, sp)] m m' -> AINV_A E m').
  { intros m' MU'. apply (AINV_A_munch E _ m m' OK AI MU'). apply Forall_cons; [cbn [fst]; lia| apply Forall_nil]. }
  assert (CCW : forall m', munch [(sp - 64, sp)] m m' -> client_consts m').
  { intros m' MU'. apply (client_consts_munch _ m m' CC MU'). intros x Hx. cbn [outside]. split; [lia| exact I]. }
  assert (SHBW : forall m', munch [(sp - 64, sp)] m m' -> wmono bsegs m m' -> shb_cells m').
  { intros m' MU' _. destruct (CCW m' MU') as (G1 & G2 & _). exact (conj G1 G2). }
  assert (SZN : forall m', munch [(sp - 64, sp)] m m' -> wmono bsegs m m' -> shz m' EL 16).
  { intros m' MU' _. apply (shz_munch _ m m' EL 16 SZN0 MU'); [| lia| lia].
    intros x Hx. cbn [outside]. split; [Z.div_mod_to_equations; lia| exact I]. }
  assert (SZT : forall m', munch [(sp - 64, sp)] m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)).
  { intros m' MU' _. apply (shz_munch _ m m' (ae_TAPE E) (8 * ae_n E) SZT0 MU'); [| lia| lia].
    intros x Hx. cbn [outside]. split; [Z.div_mod_to_equations; lia| exact I]. }
  clear SZN0 SZT0.
  pose proof (munch_refl [(sp - 64, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz sp) = sp) by (apply unsigned_lit; lia).

  astep. carve_frame 48%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 6 lstep.

  pose proof (SHBW _ MU WM) as [G1 G2].
  astep. step. step. astep.
  name_mem m1.

  chk0 SZN EL. step. if_false.
  step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
  astep. chk0 SZN (EL + 8). step. if_false. step. zstep.
  lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
  lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
  eapply (tix_cpsB E _ m1 F fc (sp + -48) i 0xb0258); [exact OK| exact (AIW m1 MU)| exact (CCW m1 MU)| lia| exact ST1| lia| unfold USTACK_TOP, SEGTOP_A; lia| exact MI1| lia| reflexivity|].
  clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
  transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
  pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
  pose proof (tape_read m2 (ae_TAPE E) (ae_tws E) i TAPEB2 ltac:(lia)) as RDT1.

  astep. chk0 SZT (ae_TAPE E + 8 * i). step. if_false.
  shz_pose SZN EL. step. shz_norm. step. if_false.

  step. step. astep. astep. astep. astep. astep. astep.
  replace (Z.land (Z.b2z (0 <? ae_DOC E)) (Z.b2z (ae_DOC E mod 8 <? 1))) with 1 by (rewrite D8; replace (0 <? ae_DOC E) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  lazymatch goal with H : rw_cells bsegs m2 (sp + -48) _ |- _ => rename H into FR2 end.

  assert (EPI : forall (mx : mem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    munch [(sp - 64, sp)] m mx -> wmono bsegs m mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (sp + -48) ->
    rw_cells bsegs mx (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt bsegs POST
      (MS (mkR x1 (wz (sp + -48)) gp (wz TPV) x5 x6 x7 (wz (EL + 8)) (wz EL) (wz 0) x11 x12 x13 x14 x15 x16 x17
               (wz SHB) (wz (shad (EL + 8))) (wz (shad EL)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          (bvmap_set 10 (wz (ae_T E (i + 1))) F) (wz 0xb02c8) fc None mx (seg_rom bsegs))).
  { intros until x31. intros MUx WMx MIx STx FRx.
    do 6 step. astep. release_frame FRx STx sp. step.
    apply evt_done. unfold POST. do 14 eexists. exists mx.
    split; [atp_st_eq_goal|]. split; [exact MUx|]. split; [exact WMx|]. split; [exact MIx|]. split; [assumption| exact (AIW mx MUx)]. }

  step. if_cases K1; zify_cond K1.
  - exfalso. first [apply K1; exact TI| apply K1; rewrite TI; reflexivity| rewrite TI in K1; unfold tword, t_dbl in K1; lia].
  - step. if_false. shz_pose SZN (EL + 8). step. shz_norm. step. if_false. step. astep. zstep.
    lazymatch goal with H : stk bsegs m2 _ _ |- _ => rename H into ST2' end.
    eapply (tix_cpsB E _ m2 F fc (sp + -48) (i + 1) 0xb02b0); [exact OK| exact (AIW m2 MU)| exact (CCW m2 MU)| lia| exact ST2'| lia| unfold USTACK_TOP, SEGTOP_A; lia| exact MI2| lia| reflexivity|].
    clear ST2' MI2 TAPEB2 RDT1. intros m3 za1 za3 za4 MU23 WM23 MI3 ST3.
    transport_after_call bsegs m2 m3 MU23 WM23. clear MU23 WM23.
    pose proof (AIW m3 MU) as (TAPEB3 & _ & _ & _ & _).
    pose proof (tape_read m3 (ae_TAPE E) (ae_tws E) (i + 1) TAPEB3 ltac:(lia)) as RDT2.

    chk0 SZT (ae_TAPE E + 8 * (i + 1)). step. if_false. step. astep.
    lazymatch goal with H : rw_cells bsegs m3 (sp + -48) _ |- _ => rename H into FR3 end.
    eapply EPI; [exact MU| exact WM| exact MI3| exact ST3| exact FR3].
Qed.
