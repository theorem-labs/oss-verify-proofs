(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface Malloc_ifaceP ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun KStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit
     Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_writec Fz_W3_iface Fz_W2_rep Fz_W2_writeg Fz_W3_defs Fz_W3_lems Fz_I3_glue.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs Fz_W7_x Fz_W7_f Fz_W7_w Fz_W7_p Fz_W7_q Fz_W7_e.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Ltac enred7 := cbn [w_ra w_sp w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_s w_CLB w_LB w_L w_m w_lo w_B w_D w_d w_pe w_E w_enm w_LBL].

Section W7. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.

  (* [comment removed for export] *)
  Variable C : cli_sig.
  Variable REST : mem -> Prop.
  Variable rest_fp : Z -> Prop.
  Hypothesis cli_open7 : forall m CLB, CLI C m CLB -> exists (pe : bptr) (E : Z) (LBL : list block),
      In (pe, E, 904) CLB /\ ~ In pe (map blk_id LBL) /\ incl_blocks LBL CLB /\ libenv m LBL E /\ errst_at_rest E [] m /\ REST m.
  Hypothesis cli_close7 : forall m CLB (pe : bptr) (E : Z) (LBL : list block),
      In (pe, E, 904) CLB -> ~ In pe (map blk_id LBL) -> incl_blocks LBL CLB -> libenv m LBL E -> errst_at_rest E [] m -> REST m -> CLI C m CLB.
  Hypothesis rest_agree : forall m m', REST m -> agree_on rest_fp m m' -> REST m'.
  Hypothesis rest_fp_where : forall a, rest_fp a -> 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS.

  Theorem rfuzz_one_proof :
    bio_new_mem_stmt libenv -> bio_write_stmt -> bio_write0_stmt -> bio_writeg_stmt -> pem_read_bio_stmt libenv errst_at_rest errst_live ->
    bio_free_mem_stmt libenv -> err_clear_steady_stmt libenv errst_at_rest errst_live -> crypto_free_stmt -> crypto_secure_free_stmt ->
    rfuzz_one_stmt C.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BNEW BW BW0 BWG PEM BF ECL CF CSF. unfold rfuzz_one_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s CLB LB D d flags lo B errv canary L
           HP LXS FL SEW SSP AV SPB HB ST LO GLO SLO ERR TP MI AL PAY FC -> -> CL CREL.
    destruct (cli_open7 m CLB CL) as (pe & E & LBL & INEC & NPEL & INCLC & LE & ER0 & RST).
    pose proof CREL as [REL ROOM].
    assert (INL : exists enm, In (pe, enm) L).
    { assert (X : In pe (map fst L)) by (rewrite <- REL; apply in_map_iff; exists (pe, E, 904); split; [reflexivity| exact INEC]).
      apply in_map_iff in X. destruct X as ([pe' enm] & Ep & Hin). cbn [fst] in Ep. subst pe'. exists enm. exact Hin. }
    destruct INL as [enm INL].
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HP) as NDE.
    assert (NLB : forall b, In b LB -> pe <> blk_id b).
    { intros b Hb Eb. rewrite map_app in NDE. apply (nodup_app_disj _ _ pe NDE); [rewrite Eb; apply in_map; exact Hb| apply in_map_iff; exists (pe, E, 904); split; [reflexivity| exact INEC]]. }
    (* [comment removed for export] *)
    pose proof (X7_proof libenv errst_at_rest errst_live errst_fp errst_live_agree errst_fp_where BF ECL) as X7P.
    pose proof (F7_proof libenv errst_at_rest errst_live
                  (FP7_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_live_agree errst_fp_where CF X7P)
                  (FS7_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_live_agree errst_fp_where CSF X7P)) as F7P.
    pose proof (PW4_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_live_agree errst_fp_where BWG F7P) as PW4P.
    pose proof (PW3_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_live_agree errst_fp_where BW0 BWG PW4P) as PW3P.
    pose proof (PW2_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_live_agree errst_fp_where BW0 BWG PW3P) as PW2P.
    pose proof (PZ7_proof libenv errst_at_rest errst_live F7P) as PZ7P.
    pose proof (E7_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_fp_where BNEW BW PEM PW2P PZ7P) as E7P.
    set (en := W7E ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s CLB LB L m lo B D d pe E enm LBL).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    unfold fuzz_one. eapply climpl_close_bind.
    { (* [comment removed for export] *)
      pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold LX_FUZZ.
      cbv delta [MallocRep.wz]. cprefix. ths. chere. eapply (E7P en flags). unfold w7_pre, w_SP, w_LBall. unfold en. enred7.
      repeat match goal with |- _ /\ _ => split end; try assumption. exists errv. exact ERR. }
    cbv beta. intros f' L' s' ms' POST. unfold w7_post, w_SP, w_LBall in POST. unfold en in POST. revert POST. enred7.
    intros (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & LBall' & -> & CST' & FRM' & PERM' & LE' & ER' & INE').
    assert (ROOM' : cntA L' + CL_ROOM_A <= CAP_A /\ cntB L' + CL_ROOM_B <= CAP_B /\ bigsum L' + CL_ROOM_BIG <= BIG_ROOM).
    { rewrite (cntA_perm _ _ PERM'), (cntB_perm _ _ PERM'), (bigsum_perm _ _ PERM'). exact ROOM. }
    destruct (call_exit (eq pe) [] s CLB LB L m s' LBall' L' m' sp tp lo B canary CST' FRM' ltac:(intros a []) ltac:(intros b Hb; exact (NLB b Hb)) HP SEW SSP HB ROOM')
      as (CLB' & errv' & PERMB & REL' & ENV & PRES & SO & FA).
    apply implM_ret. apply evt_done. exists CLB'. split; [reflexivity|]. split; [exact REL'|].
    unfold rfuzz_ret. exists u0, u1, u2, (Z_to_bv 64 0), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m'.
    split; [reflexivity|].
    split. { split; [exists errv'; exact ENV|]. split; [exact FC|]. split; [exact PRES|]. split; [exact SO| exact FA]. }
    split; [reflexivity|].
    pose proof FRM' as (CFR & [KB _] & _).
    assert (TOC : forall b, In b LBall' -> In b CLB -> In b CLB').
    { intros b Hb HbC. pose proof (Permutation_in _ PERMB Hb) as X. apply in_app_iff in X. destruct X as [X|X]; [exact X|]. exfalso.
      rewrite map_app in NDE. apply (nodup_app_disj _ _ (blk_id b) NDE); [apply in_map; exact X| apply in_map; exact HbC]. }
    split.
    - eapply (cli_close7 m' CLB' pe E LBL).
      + exact (TOC _ INE' INEC).
      + exact NPEL.
      + intros b Hb. apply TOC; [| exact (INCLC b Hb)]. apply KB; [apply in_or_app; left; exact (INCLC b Hb)|]. intros Eb. apply NPEL. rewrite Eb. apply in_map. exact Hb.
      + exact LE'.
      + exact ER'.
      + eapply rest_agree; [exact RST|]. eapply agree_on_mono; [exact CFR|]. intros a Ha. destruct (rest_fp_where a Ha) as (R1 & R2 & R3). right; right.
        split; [exact R1|]. split; [exact R2|]. split; [exact R3| intros []].
    - destruct PAY as (PB & PR & D0 & D63 & D26 & PBLK). split; [| split; [exact PR| split; [exact D0| split; [exact D63| split; [exact D26| exact PBLK]]]]].
      destruct PBLK as [ED|(pb & INpb & PB1 & PB2)].
      + eapply bytes_at_agree; [exact CFR| exact PB|]. intros a Ha. exfalso. rewrite ED in Ha. cbn in Ha. clear - Ha. lia.
      + eapply bytes_at_agree; [exact CFR| exact PB|]. intros a Ha. right; left. exists pb.
        split; [apply in_or_app; right; exact INpb|]. split; [exact (NLB _ INpb)|].
        unfold to_bytes in Ha. rewrite length_map in Ha. unfold zlength in PB2. clear - Ha PB1 PB2. lia.
  Qed.
End W7.
