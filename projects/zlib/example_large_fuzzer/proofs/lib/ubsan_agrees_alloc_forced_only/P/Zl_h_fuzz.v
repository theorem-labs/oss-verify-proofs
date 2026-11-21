(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RCalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL ZInstL ZTargetL Target Driver Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Zl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapiL.

Section FZ.
  Hypothesis CALLOC : rcalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis TDEF : rtest_large_deflate_stmt.
  Hypothesis TINF : rtest_large_inflate_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  (* [comment removed for export] *)
  Lemma size_testL : forall n, 0 <= n < 2^30 ->
    (Z.land (n + -524289) 18446744073709551615 < 18446744073709027328 <-> n < 1 \/ 524288 < n).
  Proof.
    intros n Hn. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    destruct (Z.le_gt_cases 524289 n) as [G|G].
    - rewrite Z.mod_small by lia. lia.
    - replace ((n + -524289) mod 2^64) with (n + -524289 + 2^64) by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_ret : forall (ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (Q : machine_state -> Prop),
    rw_cells psegs m (bv_unsigned sp + -32) [C8 S2; C8 S1; C8 S0; C8 ra] ->
    stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp + -32 -> mem_inv psegs m -> bv_unsigned sp < 2^63 -> 32 <= bv_unsigned sp ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6', stk psegs m lo (bv_unsigned sp) ->
       Q (MS (mkR ra sp gp tp t0' t1' t2' S0 S1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom psegs))) ->
    evt psegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1623c) fc None m (seg_rom psegs)).
  Proof.
    intros until Q. intros FR ST LO MI SPH SPL KK.
    do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. apply KK. exact ST.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_exit : forall (ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0 s : PState) (LB LK : list block) (D : Z) (d : list Z) (diff' : Z) (lo B : Z) (errv canary : word),
    lx_env m s LK LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv canary ->
    rw_cells psegs m (bv_unsigned sp + -32) [C8 S2; C8 S1; C8 S0; C8 ra] ->
    lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m0 m -> ps_so s = ps_so s0 -> ps_fa s = ps_fa s0 -> frm0 fc ->
    (length LK <= 7)%nat -> payload_ok m LB D d -> zhl_diff m diff' -> 0 <= diff' < 2^32 ->
    bv_unsigned sp <= B -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    evt psegs (rfuzz_oneL_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB D d lo B canary m0 (0, diff') s)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1623c) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. intros ENV FR PRES ESO EFA FRM LKL POK DIF DIFR' SPB LOSP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & B63 & ST & LOC & _ & _ & _ & MI).
    unfold LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in LOSP.
    rewrite unsigned_lit in ST by lia.
    eapply fz_ret; [exact FR| exact ST| lia| exact MI| lia| lia|]. intros. unfold rfuzz_oneL_post.
    do 15 eexists. exists F, fc, m, LK. split; [reflexivity|].
    split; [| split; [exact LKL| split; [reflexivity| split; [reflexivity| split; [exact POK| split; [exact DIF| exact DIFR']]]]]].
    unfold lx_post_env. split; [exists errv; eapply lx_env_sp; [exact ENV| assumption| exact SPB]|].
    split; [exact FRM|]. split; [exact PRES|]. split; [exact ESO| exact EFA].
  Qed.

  Theorem fz_mainL : rfuzz_oneL_stmt.
  Proof.
    unfold rfuzz_oneL_stmt. intros until canary.
    intros HP0 LXS0 ZLS0 SEW0 SSP0 AUX0 SPB B63 ST0 LOC LOG LOSP ERR0 TP MI0 SP16 POK0 DIF0 DIFR FRM -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOSP as LOSP0. unfold LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    pose proof POK0 as (DBY0 & DR & D0 & D63 & D30 & PIN0).
    assert (DL0 : 0 <= zlength d) by (unfold zlength; lia).
    assert (ENV0 : lx_env m s [] LB sp tp B lo errv canary).
    { unfold lx_env. cbn [app]. unfold GLOBALS_TOP. repeat (split; [eassumption|]). eassumption. }
    (* [comment removed for export] *)
    assert (PAYR : forall a, D <= a < D + zlength d -> a < lo /\ (a < 0x10000 \/ 0x5c000 <= a) /\ in_block LB a).
    { intros a Ha. destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in Ha; unfold zlength in Ha; cbn in Ha; lia|].
      pose proof (HBR _ _ _ _ HP0 Hbd) as (_ & _ & _ & BC & BI). split; [lia|]. split; [lia|]. exists bd. split; [exact Hbd| lia]. }
    pose proof ZLS0 as (_ & _ & (v1 & v2 & ZHC) & MRP). unfold ZH_STATICS in ZHC. unfold ZL_MREPL in MRP. cbv beta delta [MallocRep.wz] in MRP.
    unfold zhl_diff, ZHL_DIFF, ZH_STATICS in DIF0. cbv beta delta [MallocRep.wz] in DIF0.
    unfold fuzz_oneL. cbn [bind ret lops Target.ops lib_malloc lib_free].
    unfold LX_FUZZ. cbv beta delta [MallocRep.wz].
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (ZH_STATICS, ZH_STATICS + 16)] m) as MU. pose proof (wmono_refl psegs m) as WM. unfold ZH_STATICS in MU.
    assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
    unfold implM. iprefix.
    do 4 zstep. if_cases KSZ; zify_cond KSZ.
    { (* [comment removed for export] *)
      apply (size_testL (zlength d) ltac:(lia)) in KSZ.
      replace ((zlength d <? 1) || (ZL_MAX <? zlength d)) with true by (symmetry; apply orb_true_iff; unfold ZL_MAX; destruct KSZ; [left; apply Z.ltb_lt| right; apply Z.ltb_lt]; lia).
      zstep. zstep. apply evt_done. apply impl_ret_ok. apply evt_done.
      unfold rfuzz_oneL_post. do 15 eexists. exists F, fc, m, (@nil block). split; [reflexivity|].
      split; [| split; [cbn; lia| split; [reflexivity| split; [reflexivity| split; [exact POK0| split; [unfold zhl_diff, ZHL_DIFF, ZH_STATICS; cbv beta delta [MallocRep.wz]; exact DIF0| exact DIFR]]]]]].
      unfold lx_post_env. split; [exists errv; exact ENV0|]. split; [exact FRM|]. split; [apply lx_pres_refl|]. split; reflexivity. }
    assert (SZ : 1 <= zlength d <= ZL_MAX).
    { unfold ZL_MAX. pose proof (size_testL (zlength d) ltac:(lia)) as [_ STT].
      destruct (Z.lt_ge_cases (zlength d) 1) as [X|X]; [exfalso; pose proof (STT (or_introl X)); lia|].
      destruct (Z.lt_ge_cases 524288 (zlength d)) as [Y|Y]; [exfalso; pose proof (STT (or_intror Y)); lia| lia]. }
    replace ((zlength d <? 1) || (ZL_MAX <? zlength d)) with false by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
    cbv zeta. unfold ZL_MAX in SZ.
    set (N := NofL (zlength d)) in *. assert (EN : N = 3 * zlength d + 100) by (unfold N, NofL; lia).
    (* [comment removed for export] *)
    carve_frame 32%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 32 junk [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 zstep. do 4 zstep. zstep.
    replace (zlength d ≪ 1 + zlength d + 100) with N by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (OWN : lx_env m1 s [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv canary
                  /\ lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m m1 /\ payload_ok m1 LB D d).
    { split; [| split].
      - eapply (lx_env_munch_gen _ m m1); [exact HFRAME| exact ENV0| exact MU| exact WM| assumption| rewrite unsigned_lit by lia; exact ST0| rewrite unsigned_lit by lia; lia| | | | ].
        + constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd].
          unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        + intros a Ha. cbn [outside]. unfold ZH_STATICS, stderr_addr in Ha. lia.
        + eapply stderr_wfile0_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SEW0]. intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia.
        + exists v1, (Z_to_bv 64 D). exact ZHC.
      - eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
        + lia.
        + pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & BI). lia.
        + split; [lia|]. split; [| exact I]. intros Hz. apply HX. cbn [rin_ivs]. left. unfold LXW_ZH, ZH_STATICS. cbn [fst snd]. lia.
      - eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact POK0|]. intros a Ha. destruct (PAYR a Ha) as (P1 & P2 & _). cbn [outside]. lia. }
    destruct OWN as (ENV1 & PRES1 & POK1).
    assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (SPM : (bv_unsigned sp + -32) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    set (WLD := fun (mm : mem) (ss : PState) =>
                  rw_cells psegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
                  /\ lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m mm /\ ps_so ss = ps_so s /\ ps_fa ss = ps_fa s
                  /\ payload_ok mm LB D d /\ rw_cells psegs mm 0x5ae50 [C4 (Z_to_bv 64 0)]).
    assert (WLD1 : WLD m1 s).
    { unfold WLD. split; [exact FR|]. split; [exact PRES1|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact POK1| exact MRP]. }
    (* [comment removed for export] *)
    assert (WLD_heap : forall L mm mm' ss ss' dv, WLD mm ss -> rw_cells psegs mm 239312 [C4 (Z_to_bv 64 dv)] ->
                         rheap_pres L (bv_unsigned sp + -32) mm mm' -> (forall b, In b LB -> In b L) ->
                         ps_so ss' = ps_so ss -> ps_fa ss' = ps_fa ss -> WLD mm' ss' /\ rw_cells psegs mm' 239312 [C4 (Z_to_bv 64 dv)]).
    { intros L mm mm' ss ss' dv (FRm & PRm & ESOm & EFAm & POKm & MRPm) DIFm HPR HL ESO' EFA'.
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG.
      unfold WLD. split; [| eapply rw_cells_agree; [exact AG| exact DIFm|]; intros a Ha; cbn in Ha; right; left; split; [lia|];
                           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      split; [eapply rw_cells_agree; [exact AG| exact FRm| intros a Ha; left; cbn in Ha; lia]|].
      split. { eapply lx_pres_trans; [exact PRm|]. eapply lx_pres_weaken; [apply (lx_pres_of_heap_pres L _ [LXW_ZH; LXW_STDERR]); exact HPR| lia| exact HL| auto]. }
      split; [rewrite ESO'; exact ESOm|]. split; [rewrite EFA'; exact EFAm|].
      split. { eapply payload_ok_agree; [exact AG| exact POKm|]. intros a Ha. destruct (PAYR a Ha) as (_ & _ & (b & Hb & Hr)). right; right. exists b. split; [apply HL; exact Hb| exact Hr]. }
      eapply rw_cells_agree; [exact AG| exact MRPm|]. intros a Ha. cbn in Ha. right; left. split; [lia|].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    pose proof ENV1 as (HP1 & _ & _ & _ & _ & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI1). cbn [app] in HP1.
    set (RP := rfuzz_oneL_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m).
    (* [comment removed for export] *)
    assert (EXIT : forall mm ss LK errvx dv (x1 w0 w1 w2 s0v s1v e0 e1 e2 e3 e4 e5 e6 e7 s2v w3 w4 w5 w6 : word) Fx fcx,
               lx_env mm ss LK LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errvx canary -> WLD mm ss ->
               rw_cells psegs mm 239312 [C4 (Z_to_bv 64 dv)] -> 0 <= dv < 2^32 -> frm0 fcx -> (length LK <= 7)%nat ->
               evt psegs (RP (0, dv) ss)
                   (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp w0 w1 w2 s0v s1v e0 e1 e2 e3 e4 e5 e6 e7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                       Fx (Z_to_bv 64 0x1623c) fcx None mm (seg_rom psegs))).
    { intros until fcx. intros ENVx (FRx & PRx & ESOx & EFAx & POKx & _) DIFx DVR FRMx LKL.
      eapply fz_exit; [exact ENVx| exact FRx| exact PRx| exact ESOx| exact EFAx| exact FRMx| exact LKL| exact POKx| | exact DVR| exact SPB| exact LOSP0].
      unfold zhl_diff, ZHL_DIFF, ZH_STATICS. cbv beta delta [MallocRep.wz]. exact DIFx. }
    assert (NR : 0 < N < 2^32) by lia.
    (* [comment removed for export] *)
    do 3 zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s RP msx) end.
    eapply implM_bind.
    { eapply (CALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB N lo B errv);
        rewrite ?E32; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
        [ exact HP1 | exact AUX1 | lia | rewrite E32 in ST1; exact ST1 | exact LOC | lia | exact ERR1 | exact MRP | exact MI1 | exact TP | reflexivity | reflexivity | exact NR ]. }
    cbv beta. intros r ss2 ms2 PO. unfold rcalloc_post in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR2 & EFA2 & ESO2 & RES).
    replace (ret_pc (Z_to_bv 64 0x161e8)) with (Z_to_bv 64 0x161e8) by (symmetry; rpc).
    destruct (WLD_heap LB _ _ _ ss2 diff WLD1 DIF0 ltac:(rewrite E32 in HPR2; exact HPR2) ltac:(auto) ESO2 EFA2) as [WLD2 DIF2].
    destruct r as [cp|].
    2:{ (* S3b (#16543): the first calloc failed; the second calloc still runs; then both pointers are freed *)
      destruct RES as [-> HP2].
      assert (ENV2 : lx_env m2 ss2 [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv2 canary) by (eapply lx_env_heap; [exact ENV1| exact HPR2| exact HP2| exact MI2| exact ST2| exact ERR2| exact AUX2]).
      destruct WLD2 as (FR2 & WREST2). pose proof WREST2 as (_ & _ & _ & _ & MRP2).
      rewrite E32 in ST2.
      unfold implM. iprefix.
      do 4 zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss2 RP msx) end.
      eapply implM_bind.
      { eapply (CALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 ss2 LB N lo B errv2);
          rewrite ?E32; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
          [ exact HP2 | exact AUX2 | lia | exact ST2 | exact LOC | lia | exact ERR2 | exact MRP2 | exact MI2 | exact TP | reflexivity | reflexivity | exact NR ]. }
      cbv beta. intros r ss3 ms3 PO. unfold rcalloc_post in PO.
      destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & EFA3 & ESO3 & RES).
      replace (ret_pc (Z_to_bv 64 0x161f8)) with (Z_to_bv 64 0x161f8) by (symmetry; rpc).
      destruct (WLD_heap LB m2 m3 ss2 ss3 diff (conj FR2 WREST2) DIF2 ltac:(rewrite E32 in HPR3; exact HPR3) ltac:(auto) ESO3 EFA3) as [WLD3 DIF3].
      destruct r as [up|].
      - (* the second calloc succeeded: beqz s1 is taken; free(NULL), then free(up) *)
        destruct RES as (U & -> & UR & HP3 & UZ3).
        assert (ENV3 : lx_env m3 ss3 [(up, U, N)] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv3 canary) by (eapply lx_env_heap; [exact ENV2| exact HPR3| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
        rewrite E32 in ST3.
        apply implM_ret_bind.
        unfold implM. iprefix.
        zstep. zstep. if_true. do 2 zstep.
        eapply evt_cut; [apply rfree_null_spec; reflexivity|]. cbv beta. intros ms4 ->.
        replace (ret_pc (Z_to_bv 64 0x16234)) with (Z_to_bv 64 0x16234) by (symmetry; rpc).
        do 2 zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
        eapply implM_bind.
        { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 ss3 _ up U N lo B errv3);
            rewrite ?E32; unfold RFREE_STACK;
            [ exact HP3 | left; reflexivity | exact AUX3 | lia | exact ST3 | exact LOC | lia | exact ERR3 | exact MI3 | exact TP | reflexivity ]. }
        cbv beta. intros [] ss4 ms4 PO.
        destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & EFA4 & ESO4 & HP4).
        replace (ret_pc (Z_to_bv 64 0x1623c)) with (Z_to_bv 64 0x1623c) by (symmetry; rpc).
        rewrite (lb_remove_head up U N _ (HND _ _ _ HP3)) in HPR4, HP4.
        assert (ENV4 : lx_env m4 ss4 [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv3 canary) by (eapply (lx_env_heap m3 m4 ss3 ss4); [exact ENV3| exact HPR4| exact HP4| exact MI4| exact ST4| exact ERR4| exact AUX4]).
        rewrite E32 in HPR4.
        destruct (WLD_heap LB m3 m4 ss3 ss4 diff WLD3 DIF3 HPR4 ltac:(auto) ESO4 EFA4) as [WLD4 DIF4].
        apply implM_ret. eapply EXIT; [exact ENV4| exact WLD4| exact DIF4| exact DIFR| exact FRM| cbn; lia].
      - (* the second calloc failed too: beqz s1 is taken; free(NULL) twice *)
        destruct RES as [-> HP3].
        assert (ENV3 : lx_env m3 ss3 [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv3 canary) by (eapply lx_env_heap; [exact ENV2| exact HPR3| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
        apply implM_ret_bind. apply implM_ret_bind. apply implM_ret.
        zstep. zstep. if_true. do 2 zstep.
        eapply evt_cut; [apply rfree_null_spec; reflexivity|]. cbv beta. intros ms4 ->.
        replace (ret_pc (Z_to_bv 64 0x16234)) with (Z_to_bv 64 0x16234) by (symmetry; rpc).
        do 2 zstep.
        eapply evt_cut; [apply rfree_null_spec; reflexivity|]. cbv beta. intros ms5 ->.
        replace (ret_pc (Z_to_bv 64 0x1623c)) with (Z_to_bv 64 0x1623c) by (symmetry; rpc).
        eapply EXIT; [exact ENV3| exact WLD3| exact DIF3| exact DIFR| exact FRM| cbn; lia]. }
    destruct RES as (C & -> & CR & HP2 & CZ2).
    pose proof CR as (C0 & _ & _ & CC & CI).
    assert (ENV2 : lx_env m2 ss2 [(cp, C, N)] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv2 canary) by (eapply lx_env_heap; [exact ENV1| exact HPR2| exact HP2| exact MI2| exact ST2| exact ERR2| exact AUX2]).
    destruct WLD2 as (FR2 & WREST2). pose proof WREST2 as (_ & _ & _ & _ & MRP2).
    rewrite E32 in ST2.
    (* [comment removed for export] *)
    unfold implM. iprefix.
    do 4 zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss2 RP msx) end.
    eapply implM_bind.
    { eapply (CALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 ss2 ((cp, C, N) :: LB) N lo B errv2);
        rewrite ?E32; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
        [ exact HP2 | exact AUX2 | lia | exact ST2 | exact LOC | lia | exact ERR2 | exact MRP2 | exact MI2 | exact TP | reflexivity | reflexivity | exact NR ]. }
    cbv beta. intros r ss3 ms3 PO. unfold rcalloc_post in PO.
    destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & EFA3 & ESO3 & RES).
    replace (ret_pc (Z_to_bv 64 0x161f8)) with (Z_to_bv 64 0x161f8) by (symmetry; rpc).
    rewrite E32 in HPR3.
    destruct (WLD_heap ((cp, C, N) :: LB) m2 m3 ss2 ss3 diff (conj FR2 WREST2) DIF2 HPR3 ltac:(intros b Hb; right; exact Hb) ESO3 EFA3) as [WLD3 DIF3].
    assert (HPR3' : rheap_pres LB (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32))) m2 m3) by (rewrite E32; eapply rheap_pres_weaken; [exact HPR3| lia| intros b Hb; right; exact Hb]).
    destruct r as [up|].
    2:{ (* S3b (#16543): the second calloc failed: beqz s1 falls through, beqz s2 is taken; free(cp), then free(NULL) *)
      destruct RES as [-> HP3].
      assert (ENV3 : lx_env m3 ss3 [(cp, C, N)] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv3 canary) by (eapply lx_env_heap; [exact ENV2| exact HPR3'| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
      rewrite E32 in ST3.
      unfold implM. iprefix.
      zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|]. zstep. if_true. do 2 zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
      eapply implM_bind.
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 ss3 _ cp C N lo B errv3);
          rewrite ?E32; unfold RFREE_STACK;
          [ exact HP3 | left; reflexivity | exact AUX3 | lia | exact ST3 | exact LOC | lia | exact ERR3 | exact MI3 | exact TP | reflexivity ]. }
      cbv beta. intros [] ss4 ms4 PO.
      destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & EFA4 & ESO4 & HP4).
      replace (ret_pc (Z_to_bv 64 0x16234)) with (Z_to_bv 64 0x16234) by (symmetry; rpc).
      rewrite (lb_remove_head cp C N _ (HND _ _ _ HP3)) in HPR4, HP4.
      assert (ENV4 : lx_env m4 ss4 [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv3 canary) by (eapply (lx_env_heap m3 m4 ss3 ss4); [exact ENV3| exact HPR4| exact HP4| exact MI4| exact ST4| exact ERR4| exact AUX4]).
      rewrite E32 in HPR4.
      destruct (WLD_heap LB m3 m4 ss3 ss4 diff WLD3 DIF3 HPR4 ltac:(auto) ESO4 EFA4) as [WLD4 DIF4].
      apply implM_ret_bind. apply implM_ret.
      do 2 zstep.
      eapply evt_cut; [apply rfree_null_spec; reflexivity|]. cbv beta. intros ms5 ->.
      replace (ret_pc (Z_to_bv 64 0x1623c)) with (Z_to_bv 64 0x1623c) by (symmetry; rpc).
      eapply EXIT; [exact ENV4| exact WLD4| exact DIF4| exact DIFR| exact FRM| cbn; lia]. }
    destruct RES as (U & -> & UR & HP3 & UZ3).
    pose proof UR as (U0 & _ & _ & UC & UI).
    set (LB' := (up, U, N) :: (cp, C, N) :: LB) in *.
    assert (ENV3 : lx_env m3 ss3 [] LB' (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv3 canary).
    { eapply lx_env_blocks; [eapply (lx_env_heap m2 m3 ss2 ss3 _ [(up, U, N); (cp, C, N)] LB); [exact ENV2| exact HPR3'| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]| exact HP3]. }
    rewrite E32 in ST3.
    destruct WLD3 as (FR3 & PRES3 & ESOW3 & EFAW3 & POK3 & MRP3).
    (* [comment removed for export] *)
    assert (NEQ : cp <> up).
    { pose proof (HND _ _ _ HP3) as ND. cbn [map blk_id fst] in ND. inversion ND as [|? ? NI _]; subst. intros E. apply NI. left. exact E. }
    assert (SEPC : forall b, In b LB -> blk_addr b + blk_size b <= C \/ C + N <= blk_addr b).
    { intros b Hb. pose proof (heap_sep ss2 [(cp, C, N)] LB m2 (cp, C, N) b HND HBD HP2 ltac:(left; reflexivity) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
    assert (SEPU : forall b, In b ((cp, C, N) :: LB) -> blk_addr b + blk_size b <= U \/ U + N <= blk_addr b).
    { intros b Hb. pose proof (heap_sep ss3 [(up, U, N)] ((cp, C, N) :: LB) m3 (up, U, N) b HND HBD HP3 ltac:(left; reflexivity) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
    assert (DC : D + zlength d <= C \/ C + N <= D).
    { destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in SZ; unfold zlength in SZ; cbn in SZ; lia|]. pose proof (SEPC bd Hbd). pose proof (HBR _ _ _ _ HP0 Hbd) as (_ & _ & BS & _). lia. }
    assert (DU : D + zlength d <= U \/ U + N <= D).
    { destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in SZ; unfold zlength in SZ; cbn in SZ; lia|]. pose proof (SEPU bd ltac:(right; exact Hbd)). pose proof (HBR _ _ _ _ HP0 Hbd) as (_ & _ & BS & _). lia. }
    assert (CU : U + N <= C \/ C + N <= U) by (pose proof (SEPU (cp, C, N) ltac:(left; reflexivity)) as X; cbn [blk_addr blk_size fst snd] in X; lia).
    assert (CZ3 : u8arr psegs m3 C (to_bytes (zrepeat 0 N))).
    { rewrite to_bytes_zrepeat0. apply (u8arr_of_rw_cells psegs _ _ (Z.to_nat N)). eapply rw_cells_agree; [exact (agree_of_heap_pres _ _ _ _ HPR3)| exact CZ2|].
      intros a Ha. cbn in Ha. right; right. exists (cp, C, N). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
    assert (UZ3' : u8arr psegs m3 U (to_bytes (zrepeat 0 N))) by (rewrite to_bytes_zrepeat0; apply (u8arr_of_rw_cells psegs _ _ (Z.to_nat N)); exact UZ3).
    assert (POK3' : payload_ok m3 LB' D d) by (eapply payload_ok_mono; [exact POK3| intros b Hb; right; right; exact Hb]).
    (* [comment removed for export] *)
    unfold implM. iprefix.
    zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|]. zstep. if_cases KU; zify_cond KU; [exfalso; lia|]. do 5 zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
    eapply implM_bind.
    { eapply (TDEF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 ss3 LB' C U (zlength d) N diff cp up lo B errv3 canary);
        rewrite ?E32; unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK;
        [ exact ENV3 | unfold zhl_diff, ZHL_DIFF, ZH_STATICS; cbv beta delta [MallocRep.wz]; exact DIF3 | exact DIFR | unfold ZL_MAX; exact SZ | reflexivity
        | right; left; reflexivity | exact CZ3 | left; reflexivity | exact UZ3' | exact NEQ | lia | exact SPM | exact FRM | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros [comprc diff1] ss4 ms4 PO. unfold rtest_large_deflate_post in PO. cbn [fst snd] in PO.
    destruct PO as (z0 & z1 & z2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & F4 & fc4 & m4 & LK4 & -> & ((errv4 & ENV4) & FRM4 & LXP4 & ESO4 & EFA4) & LKL4 & CARR4 & CLEN4 & DIF4 & DIFR4).
    replace (ret_pc (Z_to_bv 64 0x16218)) with (Z_to_bv 64 0x16218) by (symmetry; rpc).
    rewrite E32 in LXP4.
    (* [comment removed for export] *)
    assert (WLD_lx : forall (A n : Z) mm mm' ss ss', WLD mm ss -> lx_pres LB' (bv_unsigned sp + -32) [(A, A + n); LXW_ZH; LXW_STDERR] mm mm' ->
                       (forall b, In b LB -> blk_addr b + blk_size b <= A \/ A + n <= blk_addr b) -> (A + n <= 0x10000 \/ 0x5c000 <= A) -> A + n <= alloc_ceiling ->
                       (D + zlength d <= A \/ A + n <= D) -> ps_so ss' = ps_so ss -> ps_fa ss' = ps_fa ss -> WLD mm' ss').
    { intros A n mm mm' ss ss' (FRm & PRm & ESOm & EFAm & POKm & MRPm) LXP SEP AI AC DA ESO' EFA'.
      pose proof (agree_of_lx_pres _ _ _ _ _ LXP) as AG.
      assert (NX : forall a, (bv_unsigned sp + -32 <= a \/ (0x29000 <= a < 0x5c000 /\ ~ stderr_addr a /\ ~ (ZH_STATICS <= a < ZH_STATICS + 16))) ->
                             ~ rin_ivs [(A, A + n); LXW_ZH; LXW_STDERR] a).
      { intros a Ha. cbn [rin_ivs fst snd]. unfold LXW_ZH, LXW_STDERR, LX_STDERR_FILE, ZH_STATICS, stderr_addr in *. cbn [fst snd]. lia. }
      unfold WLD. split; [eapply rw_cells_agree; [exact AG| exact FRm|]; intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; lia]|].
      split. { eapply lx_pres_trans; [exact PRm|]. eapply lx_pres_sub; [exact LXP|]. intros a [HX Hc]. split.
               - cbn [rin_ivs fst snd]. intros [Hi|[Hi|[Hi|[]]]]; [| apply HX; cbn [rin_ivs]; left; exact Hi| apply HX; cbn [rin_ivs]; right; left; exact Hi].
                 destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| pose proof (SEP b Hb); lia| lia].
               - destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; left; exists b; split; [right; right; exact Hb| exact Hr]| right; right; exact Hc]. }
      split; [rewrite ESO'; exact ESOm|]. split; [rewrite EFA'; exact EFAm|].
      split. { eapply payload_ok_agree; [exact AG| exact POKm|]. intros a Ha. destruct (PAYR a Ha) as (P1 & P2 & (b & Hb & Hr)).
               eapply block_client; [right; right; exact Hb| exact Hr|]. pose proof (SEP b Hb). pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _).
               cbn [rin_ivs fst snd]. unfold LXW_ZH, LXW_STDERR, LX_STDERR_FILE, ZH_STATICS. cbn [fst snd]. lia. }
      eapply rw_cells_agree; [exact AG| exact MRPm|]. intros a Ha. cbn in Ha. apply zls_addr_client.
      - unfold zls_addr, ZL_MREPL. lia.
      - apply NX. right. unfold stderr_addr, ZH_STATICS. lia. }
    assert (WLD4 : WLD m4 ss4).
    { eapply (WLD_lx C N m3 m4 ss3 ss4); [| exact LXP4| exact SEPC| exact CI| exact CC| exact DC| exact ESO4| exact EFA4].
      unfold WLD. repeat (split; [assumption|]). assumption. }
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP4) as AG4.
    assert (UZ4 : u8arr psegs m4 U (to_bytes (zrepeat 0 N))).
    { eapply u8arr_agree; [exact AG4| exact UZ3'|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zrepeat in Ha. rewrite repeat_length in Ha.
      eapply block_client; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia|]. cbn [rin_ivs fst snd]. unfold LXW_ZH, LXW_STDERR, LX_STDERR_FILE, ZH_STATICS. cbn [fst snd]. lia. }
    destruct WLD4 as (FR4 & PRES4 & ESOW4 & EFAW4 & POK4 & MRP4).
    pose proof ENV4 as (HP4 & _).
    assert (ENV4' : lx_env m4 ss4 [] (LK4 ++ LB') (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv4 canary) by (eapply lx_env_blocks; [exact ENV4| exact HP4]).
    assert (UL : zlength (zrepeat 0 N) = N) by (unfold zlength, zrepeat; rewrite repeat_length; lia).
    (* [comment removed for export] *)
    unfold implM. iprefix. do 5 zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss4 RP msx) end.
    eapply implM_bind.
    { eapply (TINF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 ss4 (LK4 ++ LB') C U (zlength d) N diff1 comprc (zrepeat 0 N) cp up lo B errv4 canary);
        rewrite ?E32; unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK;
        [ exact ENV4' | exact DIF4 | exact DIFR4 | unfold ZL_MAX; exact SZ | reflexivity
        | apply in_or_app; right; right; left; reflexivity | exact CARR4 | exact CLEN4
        | apply in_or_app; right; left; reflexivity | exact UZ4 | exact UL | exact NEQ | lia | exact SPM | exact FRM4
        | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros [] ss5 ms5 PO. unfold rtest_large_inflate_post in PO.
    destruct PO as (k0 & k1 & k2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & k3 & k4 & k5 & k6 & F5 & fc5 & m5 & LK5 & -> & ((errv5 & ENV5) & FRM5 & LXP5 & ESO5 & EFA5) & LKL5).
    replace (ret_pc (Z_to_bv 64 0x1622c)) with (Z_to_bv 64 0x1622c) by (symmetry; rpc).
    rewrite E32 in LXP5.
    assert (LXP5' : lx_pres LB' (bv_unsigned sp + -32) [(U, U + N); LXW_ZH; LXW_STDERR] m4 m5).
    { eapply lx_pres_weaken; [exact LXP5| lia| intros b Hb; apply in_or_app; right; exact Hb|].
      intros a Ha. cbn [rin_ivs] in Ha |- *. destruct Ha as [Ha|[Ha|[]]]; [left; exact Ha| right; right; left; exact Ha]. }
    assert (WLD5 : WLD m5 ss5).
    { eapply (WLD_lx U N m4 m5 ss4 ss5); [| exact LXP5'| intros b Hb; apply SEPU; right; exact Hb| exact UI| exact UC| exact DU| exact ESO5| exact EFA5].
      unfold WLD. repeat (split; [assumption|]). assumption. }
    assert (DIF5 : rw_cells psegs m5 239312 [C4 (Z_to_bv 64 diff1)]).
    { unfold zhl_diff, ZHL_DIFF, ZH_STATICS in DIF4. cbv beta delta [MallocRep.wz] in DIF4.
      eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP5)| exact DIF4|]. intros a Ha. cbn in Ha. apply zls_addr_client.
      - unfold zls_addr, ZH_STATICS. lia.
      - cbn [rin_ivs fst snd]. unfold LXW_STDERR, LX_STDERR_FILE. cbn [fst snd]. lia. }
    (* [comment removed for export] *)
    pose proof ENV5 as (HP5 & _ & _ & _ & _ & AUX5 & _ & _ & ST5 & _ & _ & ERR5 & _ & MI5). rewrite E32 in ST5.
    assert (HP5' : RHEAP ss5 ((cp, C, N) :: (up, U, N) :: (LK5 ++ LK4) ++ LB) m5).
    { eapply RHEAP_perm; [exact HP5|]. unfold LB'. rewrite (app_assoc LK5 LK4). 
      eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
      eapply Permutation_trans; [apply perm_skip; apply Permutation_sym; apply Permutation_middle|]. apply perm_swap. }
    assert (ENV5' : lx_env m5 ss5 ((cp, C, N) :: (up, U, N) :: (LK5 ++ LK4)) LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv5 canary)
      by (eapply lx_env_blocks; [exact ENV5| exact HP5']).
    unfold implM. iprefix. do 2 zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss5 RP msx) end.
    eapply implM_bind.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 m5 ss5 _ cp C N lo B errv5);
        rewrite ?E32; unfold RFREE_STACK;
        [ exact HP5' | left; reflexivity | exact AUX5 | lia | exact ST5 | exact LOC | lia | exact ERR5 | exact MI5 | exact TP | reflexivity ]. }
    cbv beta. intros [] ss6 ms6 PO.
    destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPR6 & EFA6 & ESO6 & HP6).
    replace (ret_pc (Z_to_bv 64 0x16234)) with (Z_to_bv 64 0x16234) by (symmetry; rpc).
    rewrite (lb_remove_head cp C N _ (HND _ _ _ HP5')) in HPR6, HP6. rewrite E32 in HPR6.
    assert (SUB6 : forall b, In b LB -> In b ((up, U, N) :: (LK5 ++ LK4) ++ LB)) by (intros b Hb; right; apply in_or_app; right; exact Hb).
    destruct (WLD_heap _ m5 m6 ss5 ss6 diff1 WLD5 DIF5 HPR6 SUB6 ESO6 EFA6) as [WLD6 DIF6].
    assert (ENV6 : lx_env m6 ss6 ((up, U, N) :: (LK5 ++ LK4)) LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv5 canary).
    { eapply (lx_env_heap m5 m6 ss5 ss6); [exact ENV5'| rewrite E32; eapply rheap_pres_weaken; [exact HPR6| lia| exact SUB6]| exact HP6| exact MI6| exact ST6| exact ERR6| exact AUX6]. }
    rewrite E32 in ST6.
    unfold implM. iprefix. do 2 zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss6 RP msx) end.
    eapply implM_bind.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 m6 ss6 _ up U N lo B errv5);
        rewrite ?E32; unfold RFREE_STACK;
        [ exact HP6 | left; reflexivity | exact AUX6 | lia | exact ST6 | exact LOC | lia | exact ERR6 | exact MI6 | exact TP | reflexivity ]. }
    cbv beta. intros [] ss7 ms7 PO.
    destruct PO as (o0 & o1 & o2 & l0 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & o3 & o4 & o5 & o6 & m7 & -> & MI7 & ST7 & ERR7 & AUX7 & HPR7 & EFA7 & ESO7 & HP7).
    replace (ret_pc (Z_to_bv 64 0x1623c)) with (Z_to_bv 64 0x1623c) by (symmetry; rpc).
    rewrite (lb_remove_head up U N _ (HND _ _ _ HP6)) in HPR7, HP7. rewrite E32 in HPR7.
    assert (SUB7 : forall b, In b LB -> In b ((LK5 ++ LK4) ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    destruct (WLD_heap _ m6 m7 ss6 ss7 diff1 WLD6 DIF6 HPR7 SUB7 ESO7 EFA7) as [WLD7 DIF7].
    assert (ENV7 : lx_env m7 ss7 (LK5 ++ LK4) LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv5 canary).
    { eapply (lx_env_heap m6 m7 ss6 ss7); [exact ENV6| rewrite E32; eapply rheap_pres_weaken; [exact HPR7| lia| exact SUB7]| exact HP7| exact MI7| exact ST7| exact ERR7| exact AUX7]. }
    apply implM_ret.
    eapply EXIT; [exact ENV7| exact WLD7| exact DIF7| exact DIFR4| exact FRM5| rewrite length_app; lia].
  Qed.
End FZ.
End WithCeiling0.
