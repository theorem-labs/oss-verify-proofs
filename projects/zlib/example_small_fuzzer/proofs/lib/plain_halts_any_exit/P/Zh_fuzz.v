(* LLVMFuzzerTestOneInput of the google/oss-fuzz #16543 build (both callocs, then one test, then the frees) *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RCalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Exit Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Driver_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Driver_iface.Zh_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac nm n t := first [t | fail 100 "premise" n].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.

Section FZ.
  Variable R : zreps.
  Hypothesis ZOK : zlib_ok R.
  Hypothesis CALLOC : rcalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FREE0 : rfree_null_stmt.
  Hypothesis TDEF : rtest_deflate_stmt.
  Hypothesis TINF : rtest_inflate_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  Lemma size_test : forall n, 0 <= n < 2^30 ->
    (Z.land (n + -1048577) 18446744073709551615 < 18446744073708503040 <-> n < 1 \/ 1048576 < n).
  Proof.
    intros n Hn. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    destruct (Z.le_gt_cases 1048577 n) as [G|G].
    - rewrite Z.mod_small by lia. lia.
    - replace ((n + -1048577) mod 2^64) with (n + -1048577 + 2^64) by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
  Qed.

  Lemma fz_ret : forall (ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte) (lo : Z) (Q : machine_state -> Prop),
    rw_cells psegs m (bv_unsigned sp + -48) [CB 8 j0; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    stk psegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp + -48 -> mem_inv psegs m -> bv_unsigned sp < 2^63 -> 48 <= bv_unsigned sp ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6', stk psegs m lo (bv_unsigned sp) ->
       Q (MS (mkR ra sp gp tp t0' t1' t2' S0 S1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom psegs))) ->
    evt psegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x16154) fc None m (seg_rom psegs)).
  Proof.
    intros until Q. intros FR ST LO MI SPH SPL KK.
    do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. apply KK. exact ST.
  Qed.

  Lemma fz_exit : forall (ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0 s : PState) (LB LK : list block) (D : Z) (d : list Z) (j0 : list byte) (lo B : Z) (errv canary : word),
    lx_env m s LK LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv canary ->
    rw_cells psegs m (bv_unsigned sp + -48) [CB 8 j0; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m0 m -> ps_so s = ps_so s0 -> ps_fa s = ps_fa s0 -> frm0 fc ->
    (length LK <= 2)%nat -> payload_ok m LB D d ->
    bv_unsigned sp <= B -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    evt psegs (rfuzz_one_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB D d lo B canary m0 0 s)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x16154) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. intros ENV FR PRES ESO EFA FRM LKL POK SPB LOSP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & B63 & ST & LOC & _ & _ & _ & MI).
    unfold LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in LOSP.
    rewrite unsigned_lit in ST by lia.
    eapply fz_ret; [exact FR| exact ST| lia| exact MI| lia| lia|]. intros. unfold rfuzz_one_post.
    do 15 eexists. exists F, fc, m, LK. split; [reflexivity|].
    split; [| split; [exact LKL| split; [reflexivity| split; [reflexivity| exact POK]]]].
    unfold lx_post_env. split; [exists errv; eapply lx_env_sp; [exact ENV| assumption| exact SPB]|].
    split; [exact FRM|]. split; [exact PRES|]. split; [exact ESO| exact EFA].
  Qed.

  Theorem fz_main : rfuzz_one_stmt.
  Proof.
    unfold rfuzz_one_stmt. intros until canary.
    intros HP0 LXS0 ZLS0 SEW0 SSP0 AUX0 SPB B63 ST0 LOC LOG LOSP ERR0 TP MI0 SP16 POK0 FRM -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOSP as LOSP0. unfold LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct ZOK as (CBND & _).
    pose proof POK0 as (DBY0 & DR & D0 & D63 & D30 & PIN0).
    assert (DL0 : 0 <= zlength d) by (unfold zlength; lia).
    assert (ENV0 : lx_env m s [] LB sp tp B lo errv canary).
    { unfold lx_env. cbn [app]. unfold GLOBALS_TOP. repeat (split; [eassumption|]). eassumption. }
    assert (PAYR : forall a, D <= a < D + zlength d -> a < lo /\ (a < 0x10000 \/ 0x5b000 <= a) /\ in_block LB a).
    { intros a Ha. destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in Ha; unfold zlength in Ha; cbn in Ha; lia|].
      pose proof (HBR _ _ _ _ HP0 Hbd) as (_ & _ & _ & BC & BI). split; [lia|]. split; [lia|]. exists bd. split; [exact Hbd| lia]. }
    pose proof ZLS0 as (_ & _ & (v1 & v2 & ZHC) & MRP). unfold ZH_STATICS in ZHC. unfold ZL_MREPL in MRP. cbv beta delta [MallocRep.wz] in MRP.
    unfold fuzz_one. cbn [bind ret lops Target.ops lib_malloc lib_free].
    unfold LX_FUZZ. cbv beta delta [MallocRep.wz].
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ZH_STATICS, ZH_STATICS + 16)] m) as MU. pose proof (wmono_refl psegs m) as WM. unfold ZH_STATICS in MU.
    assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
    unfold implM. iprefix.
    zstep. carve_frame 48%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 48 junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 zstep. do 3 zstep. zstep.
    eapply evt_cut.
    { eapply (CBND _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (zlength d)); [lia| reflexivity| eassumption]. }
    cbv beta. intros ms1 (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & CBV).
    replace (ret_pc (Z_to_bv 64 0x160d8)) with (Z_to_bv 64 0x160d8) by (symmetry; rpc).
    assert (OWN : forall mm (w1 w2 : word), munch [(bv_unsigned sp + -48, bv_unsigned sp); (238512, 238512 + 16)] m mm -> wmono psegs m mm -> mem_inv psegs mm ->
                    stk psegs mm lo (bv_unsigned sp + -48) -> rw_cells psegs mm 238512 [C8 w1; C8 w2] ->
                    lx_env mm s [] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv canary
                    /\ lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m mm /\ payload_ok mm LB D d).
    { intros mm w1 w2 MUm WMm MIm STm ZHm.
      split; [| split].
      - eapply (lx_env_munch_gen _ m mm); [exact HFRAME| exact ENV0| exact MUm| exact WMm| exact MIm| rewrite unsigned_lit by lia; exact STm| rewrite unsigned_lit by lia; lia| | | | ].
        + constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd].
          unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        + intros a Ha. cbn [outside]. unfold ZH_STATICS, stderr_addr in Ha. lia.
        + eapply stderr_wfile0_agree; [exact (agree_on_of_munch _ _ _ MUm WMm)| | exact SEW0]. intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia.
        + exists w1, w2. exact ZHm.
      - eapply lx_pres_of_munch; [exact MUm| exact WMm|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
        + lia.
        + pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & BI). lia.
        + split; [lia|]. split; [| exact I]. intros Hz. apply HX. cbn [rin_ivs]. left. unfold LXW_ZH, ZH_STATICS. cbn [fst snd]. lia.
      - eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MUm WMm)| exact POK0|]. intros a Ha. destruct (PAYR a Ha) as (P1 & P2 & _). cbn [outside]. lia. }
    zstep. zstep. zstep. zstep. if_cases KSZ; zify_cond KSZ.
    { apply (size_test (zlength d) ltac:(lia)) in KSZ.
      replace ((zlength d <? 1) || (ZH_MAX <? zlength d)) with true by (symmetry; apply orb_true_iff; unfold ZH_MAX; destruct KSZ; [left; apply Z.ltb_lt| right; apply Z.ltb_lt]; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => destruct (OWN mx v1 v2 MU WM MI0 ST0 ZHC) as (ENV1 & PRES1 & POK1) end.
      eapply evt_mono; [eapply fz_exit; [exact ENV1| exact FR| exact PRES1| reflexivity| reflexivity| exact FRM| cbn; lia| exact POK1| exact SPB| exact LOSP0]|].
      intros ms' H'. apply impl_ret_ok. apply evt_done. exact H'. }
    assert (SZ : 1 <= zlength d <= ZH_MAX).
    { unfold ZH_MAX. pose proof (size_test (zlength d) ltac:(lia)) as [_ STT].
      destruct (Z.lt_ge_cases (zlength d) 1) as [X|X]; [exfalso; pose proof (STT (or_introl X)); lia|].
      destruct (Z.lt_ge_cases 1048576 (zlength d)) as [Y|Y]; [exfalso; pose proof (STT (or_intror Y)); lia| lia]. }
    replace ((zlength d <? 1) || (ZH_MAX <? zlength d)) with false by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge| apply Z.ltb_ge]; lia).
    cbv zeta. specialize (CBV SZ). subst b0.
    set (cl := z_bound za (zlength d)) in *.
    pose proof (zo_bound za the_zapi_ok (zlength d) SZ) as CLF. fold cl in CLF. unfold ZB_MAX, ZH_MAX in CLF, SZ.
    do 8 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (OWN m1 _ _ MU WM MI0 ST0 ZHC) as (ENV1 & PRES1 & POK1).
    assert (E48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (SPM : (bv_unsigned sp + -48) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
    set (WLD := fun (mm : mem) (ss : PState) =>
                  (exists j0, rw_cells psegs mm (bv_unsigned sp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
                  /\ lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m mm /\ ps_so ss = ps_so s /\ ps_fa ss = ps_fa s
                  /\ payload_ok mm LB D d /\ zh_statics mm D d /\ rw_cells psegs mm 0x5ab30 [C4 (Z_to_bv 64 0)]).
    assert (WLD1 : WLD m1 s).
    { unfold WLD, zh_statics, ZH_STATICS. cbv beta delta [MallocRep.wz]. split; [eexists; exact FR|]. split; [exact PRES1|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact POK1|]. split; [exact ZHC| exact MRP]. }
    assert (WLD_heap : forall L mm mm' ss ss', WLD mm ss -> rheap_pres L (bv_unsigned sp + -48) mm mm' -> (forall b, In b LB -> In b L) ->
                         ps_so ss' = ps_so ss -> ps_fa ss' = ps_fa ss -> WLD mm' ss').
    { intros L mm mm' ss ss' ((j0 & FRm) & PRm & ESOm & EFAm & POKm & ZSTm & MRPm) HPR HL ESO' EFA'.
      pose proof (agree_of_heap_pres _ _ _ _ HPR) as AG.
      unfold WLD. split; [exists j0; eapply rw_cells_agree; [exact AG| exact FRm| intros a Ha; left; cbn in Ha; lia]|].
      split. { eapply lx_pres_trans; [exact PRm|]. eapply lx_pres_weaken; [apply (lx_pres_of_heap_pres L _ [LXW_ZH; LXW_STDERR]); exact HPR| lia| exact HL| auto]. }
      split; [rewrite ESO'; exact ESOm|]. split; [rewrite EFA'; exact EFAm|].
      split. { eapply payload_ok_agree; [exact AG| exact POKm|]. intros a Ha. destruct (PAYR a Ha) as (_ & _ & (b & Hb & Hr)). right; right. exists b. split; [apply HL; exact Hb| exact Hr]. }
      split. { unfold zh_statics, ZH_STATICS in *. eapply rw_cells_agree; [exact AG| exact ZSTm|]. intros a Ha. cbn in Ha. right; left. split; [lia|].
               unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
      eapply rw_cells_agree; [exact AG| exact MRPm|]. intros a Ha. cbn in Ha. right; left. split; [lia|].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    pose proof ENV1 as (HP1 & _ & _ & _ & _ & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI1). cbn [app] in HP1.
    set (RP := rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m).
    assert (EXIT : forall mm ss LK errvx (x1 w0 w1 w2 s0v s1v e0 e1 e2 e3 e4 e5 e6 e7 s2v s3v w3 w4 w5 w6 : word) Fx fcx,
               lx_env mm ss LK LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errvx canary -> WLD mm ss -> frm0 fcx -> (length LK <= 2)%nat ->
               evt psegs (RP 0 ss)
                   (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp w0 w1 w2 s0v s1v e0 e1 e2 e3 e4 e5 e6 e7 s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                       Fx (Z_to_bv 64 0x16154) fcx None mm (seg_rom psegs))).
    { intros until fcx. intros ENVx ((j0 & FRx) & PRx & ESOx & EFAx & POKx & _) FRMx LKL.
      eapply fz_exit; [exact ENVx| exact FRx| exact PRx| exact ESOx| exact EFAx| exact FRMx| exact LKL| exact POKx| exact SPB| exact LOSP0]. }
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s RP msx) end.
    (* calloc #1: the compressed buffer *)
    eapply implM_bind.
    { eapply (CALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB cl lo B errv);
        rewrite ?E48; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
        [ exact HP1 | exact AUX1 | lia | rewrite E48 in ST1; exact ST1 | exact LOC | lia | exact ERR1 | exact MRP | exact MI1 | exact TP | reflexivity | reflexivity | lia ]. }
    cbv beta. intros r ss2 ms2 PO. unfold rcalloc_post in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR2 & EFA2 & ESO2 & RES).
    replace (ret_pc (Z_to_bv 64 0x16108)) with (Z_to_bv 64 0x16108) by (symmetry; rpc).
    pose proof (WLD_heap LB _ _ _ ss2 WLD1 ltac:(rewrite E48 in HPR2; exact HPR2) ltac:(auto) ESO2 EFA2) as WLD2.
    destruct r as [cp|].
    - (* calloc #1 gave cp *)
      destruct RES as (C & -> & CR & HP2 & CZ2).
      pose proof CR as (C0 & _ & _ & CC & CI).
      assert (ENV2 : lx_env m2 ss2 [(cp, C, cl)] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv2 canary) by (eapply lx_env_heap; [exact ENV1| exact HPR2| exact HP2| exact MI2| exact ST2| exact ERR2| exact AUX2]).
      destruct WLD2 as ((j2 & FR2) & WREST2). pose proof WREST2 as (_ & _ & _ & _ & _ & MRP2).
      rewrite E48 in ST2.
      (* mv s2,a0; li a0,1; mv a1,s0; jal calloc: no test between the two callocs *)
      unfold implM. iprefix. do 4 zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss2 RP msx) end.
      eapply implM_bind.
      { eapply (CALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 ss2 ((cp, C, cl) :: LB) (zlength d) lo B errv2);
          rewrite ?E48; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
          [ exact HP2 | exact AUX2 | lia | exact ST2 | exact LOC | lia | exact ERR2 | exact MRP2 | exact MI2 | exact TP | reflexivity | reflexivity | lia ]. }
      cbv beta. intros r2 ss3 ms3 PO. unfold rcalloc_post in PO.
      destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & EFA3 & ESO3 & RES).
      replace (ret_pc (Z_to_bv 64 0x16118)) with (Z_to_bv 64 0x16118) by (symmetry; rpc).
      rewrite E48 in HPR3.
      pose proof (WLD_heap ((cp, C, cl) :: LB) m2 m3 ss2 ss3 (conj (ex_intro _ j2 FR2) WREST2) HPR3 ltac:(intros b Hb; right; exact Hb) ESO3 EFA3) as WLD3.
      assert (HPR3' : rheap_pres LB (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48))) m2 m3) by (rewrite E48; eapply rheap_pres_weaken; [exact HPR3| lia| intros b Hb; right; exact Hb]).
      destruct r2 as [up|].
      + (* both allocated: the deflate / inflate round trip *)
        destruct RES as (U & -> & UR & HP3 & UZ3).
        pose proof UR as (U0 & _ & _ & UC & UI).
        set (LB' := (up, U, zlength d) :: (cp, C, cl) :: LB) in *.
        assert (ENV3 : lx_env m3 ss3 [] LB' (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv3 canary).
        { eapply lx_env_blocks; [eapply (lx_env_heap m2 m3 ss2 ss3 _ [(up, U, zlength d); (cp, C, cl)] LB); [exact ENV2| exact HPR3'| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]| exact HP3]. }
        rewrite E48 in ST3.
        destruct WLD3 as ((j3 & FR3) & PRES3 & ESOW3 & EFAW3 & POK3 & ZST3 & MRP3).
        assert (NEQ : cp <> up).
        { pose proof (HND _ _ _ HP3) as ND. cbn [map blk_id fst] in ND. inversion ND as [|? ? NI _]; subst. intros E. apply NI. left. exact E. }
        assert (SEPC : forall b, In b LB -> blk_addr b + blk_size b <= C \/ C + cl <= blk_addr b).
        { intros b Hb. pose proof (heap_sep ss2 [(cp, C, cl)] LB m2 (cp, C, cl) b HND HBD HP2 ltac:(left; reflexivity) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
        assert (SEPU : forall b, In b ((cp, C, cl) :: LB) -> blk_addr b + blk_size b <= U \/ U + zlength d <= blk_addr b).
        { intros b Hb. pose proof (heap_sep ss3 [(up, U, zlength d)] ((cp, C, cl) :: LB) m3 (up, U, zlength d) b HND HBD HP3 ltac:(left; reflexivity) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
        assert (DC : D + zlength d <= C \/ C + cl <= D).
        { destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in SZ; unfold zlength in SZ; cbn in SZ; lia|]. pose proof (SEPC bd Hbd). pose proof (HBR _ _ _ _ HP0 Hbd) as (_ & _ & BS & _). lia. }
        assert (DU : D + zlength d <= U \/ U + zlength d <= D).
        { destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in SZ; unfold zlength in SZ; cbn in SZ; lia|]. pose proof (SEPU bd ltac:(right; exact Hbd)). pose proof (HBR _ _ _ _ HP0 Hbd) as (_ & _ & BS & _). lia. }
        assert (CU : U + zlength d <= C \/ C + cl <= U) by (pose proof (SEPU (cp, C, cl) ltac:(left; reflexivity)) as X; cbn [blk_addr blk_size fst snd] in X; lia).
        assert (CZ3 : u8arr psegs m3 C (to_bytes (zrepeat 0 cl))).
        { rewrite to_bytes_zrepeat0. apply (u8arr_of_rw_cells psegs _ _ (Z.to_nat cl)). eapply rw_cells_agree; [exact (agree_of_heap_pres _ _ _ _ HPR3)| exact CZ2|].
          intros a Ha. cbn in Ha. right; right. exists (cp, C, cl). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
        assert (UZ3' : u8arr psegs m3 U (to_bytes (zrepeat 0 (zlength d)))) by (rewrite to_bytes_zrepeat0; apply (u8arr_of_rw_cells psegs _ _ (Z.to_nat (zlength d))); exact UZ3).
        assert (POK3' : payload_ok m3 LB' D d) by (eapply payload_ok_mono; [exact POK3| intros b Hb; right; right; exact Hb]).
        (* mv s3,a0; beqz s2 (not taken); beqz s3 (not taken); mv a0,s2; mv a1,s1; jal test_deflate *)
        unfold implM. iprefix.
        zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
        zstep. if_cases KU; zify_cond KU; [exfalso; lia|].
        do 3 zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
        eapply implM_bind.
        { eapply (TDEF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 ss3 LB' D C cl d cp lo B errv3 canary);
            rewrite ?E48; unfold ZH_TEST_STACK, LX_PRINTF_STACK;
            [ exact ENV3 | exact ZST3 | exact POK3' | exact SZ | right; left; reflexivity | exact CZ3 | reflexivity | exact DC | lia | exact SPM | exact FRM | reflexivity | reflexivity ]. }
        cbv beta. intros comprc ss4 ms4 PO. unfold rtest_deflate_post in PO.
        destruct PO as (z0 & z1 & z2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & F4 & fc4 & m4 & -> & ((errv4 & ENV4) & FRM4 & LXP4 & ESO4 & EFA4) & CARR4 & CLEN4).
        replace (ret_pc (Z_to_bv 64 0x16130)) with (Z_to_bv 64 0x16130) by (symmetry; rpc).
        rewrite E48 in LXP4.
        assert (WLD_lx : forall (A n : Z) mm mm' ss ss', WLD mm ss -> lx_pres LB' (bv_unsigned sp + -48) [(A, A + n); LXW_STDERR] mm mm' ->
                           (forall b, In b LB -> blk_addr b + blk_size b <= A \/ A + n <= blk_addr b) -> (A + n <= 0x10000 \/ 0x5b000 <= A) -> A + n <= alloc_ceiling ->
                           (D + zlength d <= A \/ A + n <= D) -> ps_so ss' = ps_so ss -> ps_fa ss' = ps_fa ss -> WLD mm' ss').
        { intros A n mm mm' ss ss' ((j0 & FRm) & PRm & ESOm & EFAm & POKm & ZSTm & MRPm) LXP SEP AI AC DA ESO' EFA'.
          pose proof (agree_of_lx_pres _ _ _ _ _ LXP) as AG.
          assert (NX : forall a, (bv_unsigned sp + -48 <= a \/ (0x28000 <= a < 0x5b000 /\ ~ stderr_addr a)) -> ~ rin_ivs [(A, A + n); LXW_STDERR] a).
          { intros a Ha. cbn [rin_ivs fst snd]. unfold LXW_STDERR, LX_STDERR_FILE, stderr_addr in *. cbn [fst snd]. lia. }
          unfold WLD. split; [exists j0; eapply rw_cells_agree; [exact AG| exact FRm|]; intros a Ha; cbn in Ha; apply stack_client; [lia| apply NX; lia]|].
          split. { eapply lx_pres_trans; [exact PRm|]. eapply lx_pres_sub; [exact LXP|]. intros a [HX Hc]. split.
                   - cbn [rin_ivs fst snd]. intros [Hi|[Hi|[]]]; [| apply HX; cbn [rin_ivs]; right; left; exact Hi].
                     destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| pose proof (SEP b Hb); lia| lia].
                   - destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; left; exists b; split; [right; right; exact Hb| exact Hr]| right; right; exact Hc]. }
          split; [rewrite ESO'; exact ESOm|]. split; [rewrite EFA'; exact EFAm|].
          split. { eapply payload_ok_agree; [exact AG| exact POKm|]. intros a Ha. destruct (PAYR a Ha) as (P1 & P2 & (b & Hb & Hr)).
                   eapply block_client; [right; right; exact Hb| exact Hr|]. cbn [rin_ivs fst snd]. unfold LXW_STDERR, LX_STDERR_FILE. cbn [fst snd]. lia. }
          split. { unfold zh_statics, ZH_STATICS in *. eapply rw_cells_agree; [exact AG| exact ZSTm|]. intros a Ha. cbn in Ha. apply zls_addr_client.
                   - unfold zls_addr, ZH_STATICS. lia.
                   - apply NX. right. unfold stderr_addr. lia. }
          eapply rw_cells_agree; [exact AG| exact MRPm|]. intros a Ha. cbn in Ha. apply zls_addr_client.
          - unfold zls_addr, ZL_MREPL. lia.
          - apply NX. right. unfold stderr_addr. lia. }
        assert (WLD4 : WLD m4 ss4).
        { eapply (WLD_lx C cl m3 m4 ss3 ss4); [| exact LXP4| exact SEPC| exact CI| exact CC| exact DC| exact ESO4| exact EFA4].
          unfold WLD. split; [exists j3; exact FR3|]. repeat (split; [assumption|]). assumption. }
        pose proof (agree_of_lx_pres _ _ _ _ _ LXP4) as AG4.
        assert (UZ4 : u8arr psegs m4 U (to_bytes (zrepeat 0 (zlength d)))).
        { eapply u8arr_agree; [exact AG4| exact UZ3'|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zrepeat in Ha. rewrite repeat_length in Ha.
          eapply block_client; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia|]. cbn [rin_ivs fst snd]. unfold LXW_STDERR, LX_STDERR_FILE. cbn [fst snd]. lia. }
        destruct WLD4 as ((j4 & FR4) & PRES4 & ESOW4 & EFAW4 & POK4 & ZST4 & MRP4).
        assert (POK4' : payload_ok m4 LB' D d) by (eapply payload_ok_mono; [exact POK4| intros b Hb; right; right; exact Hb]).
        unfold implM. iprefix. do 5 zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss4 RP msx) end.
        eapply implM_bind.
        { eapply (TINF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 ss4 LB' D C cl U (zlength d) d comprc cp up lo B errv4 canary);
            rewrite ?E48; unfold ZH_TEST_STACK, LX_PRINTF_STACK;
            [ exact ENV4 | exact ZST4 | exact POK4' | exact SZ | reflexivity | right; left; reflexivity | exact CARR4 | exact CLEN4 | reflexivity
            | left; reflexivity | exact UZ4 | exact NEQ | exact DU | lia | exact SPM | exact FRM4 | reflexivity | reflexivity | reflexivity | reflexivity ]. }
        cbv beta. intros [] ss5 ms5 PO. unfold rtest_inflate_post in PO.
        destruct PO as (k0 & k1 & k2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & k3 & k4 & k5 & k6 & F5 & fc5 & m5 & LK & -> & ((errv5 & ENV5) & FRM5 & LXP5 & ESO5 & EFA5) & LKL).
        replace (ret_pc (Z_to_bv 64 0x16144)) with (Z_to_bv 64 0x16144) by (symmetry; rpc).
        rewrite E48 in LXP5.
        assert (WLD5 : WLD m5 ss5).
        { eapply (WLD_lx U (zlength d) m4 m5 ss4 ss5); [| exact LXP5| intros b Hb; apply SEPU; right; exact Hb| exact UI| exact UC| exact DU| exact ESO5| exact EFA5].
          unfold WLD. split; [exists j4; exact FR4|]. repeat (split; [assumption|]). assumption. }
        pose proof ENV5 as (HP5 & _ & _ & _ & _ & AUX5 & _ & _ & ST5 & _ & _ & ERR5 & _ & MI5). rewrite E48 in ST5.
        assert (HP5' : RHEAP ss5 ((cp, C, cl) :: (up, U, zlength d) :: LK ++ LB) m5).
        { eapply RHEAP_perm; [exact HP5|]. unfold LB'.
          eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
          eapply Permutation_trans; [apply perm_skip; apply Permutation_sym; apply Permutation_middle|]. apply perm_swap. }
        assert (ENV5' : lx_env m5 ss5 ((cp, C, cl) :: (up, U, zlength d) :: LK) LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv5 canary)
          by (eapply lx_env_blocks; [exact ENV5| exact HP5']).
        unfold implM. iprefix. do 2 zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss5 RP msx) end.
        eapply implM_bind.
        { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 m5 ss5 _ cp C cl lo B errv5);
            rewrite ?E48; unfold RFREE_STACK;
            [ exact HP5' | left; reflexivity | exact AUX5 | lia | exact ST5 | exact LOC | lia | exact ERR5 | exact MI5 | exact TP | reflexivity ]. }
        cbv beta. intros [] ss6 ms6 PO.
        destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPR6 & EFA6 & ESO6 & HP6).
        replace (ret_pc (Z_to_bv 64 0x1614c)) with (Z_to_bv 64 0x1614c) by (symmetry; rpc).
        rewrite (lb_remove_head cp C cl _ (HND _ _ _ HP5')) in HPR6, HP6. rewrite E48 in HPR6.
        assert (SUB6 : forall b, In b LB -> In b ((up, U, zlength d) :: LK ++ LB)) by (intros b Hb; right; apply in_or_app; right; exact Hb).
        pose proof (WLD_heap _ m5 m6 ss5 ss6 WLD5 HPR6 SUB6 ESO6 EFA6) as WLD6.
        assert (ENV6 : lx_env m6 ss6 ((up, U, zlength d) :: LK) LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv5 canary).
        { eapply (lx_env_heap m5 m6 ss5 ss6); [exact ENV5'| rewrite E48; eapply rheap_pres_weaken; [exact HPR6| lia| exact SUB6]| exact HP6| exact MI6| exact ST6| exact ERR6| exact AUX6]. }
        rewrite E48 in ST6.
        unfold implM. iprefix. do 2 zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss6 RP msx) end.
        eapply implM_bind.
        { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 m6 ss6 _ up U (zlength d) lo B errv5);
            rewrite ?E48; unfold RFREE_STACK;
            [ exact HP6 | left; reflexivity | exact AUX6 | lia | exact ST6 | exact LOC | lia | exact ERR6 | exact MI6 | exact TP | reflexivity ]. }
        cbv beta. intros [] ss7 ms7 PO.
        destruct PO as (o0 & o1 & o2 & l0 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & o3 & o4 & o5 & o6 & m7 & -> & MI7 & ST7 & ERR7 & AUX7 & HPR7 & EFA7 & ESO7 & HP7).
        replace (ret_pc (Z_to_bv 64 0x16154)) with (Z_to_bv 64 0x16154) by (symmetry; rpc).
        rewrite (lb_remove_head up U (zlength d) _ (HND _ _ _ HP6)) in HPR7, HP7. rewrite E48 in HPR7.
        assert (SUB7 : forall b, In b LB -> In b (LK ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
        pose proof (WLD_heap _ m6 m7 ss6 ss7 WLD6 HPR7 SUB7 ESO7 EFA7) as WLD7.
        assert (ENV7 : lx_env m7 ss7 LK LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv5 canary).
        { eapply (lx_env_heap m6 m7 ss6 ss7); [exact ENV6| rewrite E48; eapply rheap_pres_weaken; [exact HPR7| lia| exact SUB7]| exact HP7| exact MI7| exact ST7| exact ERR7| exact AUX7]. }
        apply implM_ret.
        eapply EXIT; [exact ENV7| exact WLD7| exact FRM5| exact LKL].
      + (* cp allocated, calloc #2 NULL: free cp, free NULL, exit *)
        destruct RES as [-> HP3].
        assert (ENV3 : lx_env m3 ss3 [(cp, C, cl)] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv3 canary)
          by (eapply lx_env_heap; [exact ENV2| exact HPR3'| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
        rewrite E48 in ST3.
        (* mv s3,a0; beqz s2 (not taken); beqz s3 (taken, to 0x16144); mv a0,s2; jal free *)
        unfold implM. iprefix.
        zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
        zstep. if_true.
        do 2 zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
        eapply implM_bind.
        { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 ss3 _ cp C cl lo B errv3);
            rewrite ?E48; unfold RFREE_STACK;
            [ exact HP3 | left; reflexivity | exact AUX3 | lia | exact ST3 | exact LOC | lia | exact ERR3 | exact MI3 | exact TP | reflexivity ]. }
        cbv beta. intros [] ss4 ms4 PO.
        destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & EFA4 & ESO4 & HP4).
        replace (ret_pc (Z_to_bv 64 0x1614c)) with (Z_to_bv 64 0x1614c) by (symmetry; rpc).
        rewrite (lb_remove_head cp C cl _ (HND _ _ _ HP3)) in HPR4, HP4. rewrite E48 in HPR4.
        pose proof (WLD_heap _ m3 m4 ss3 ss4 WLD3 HPR4 ltac:(auto) ESO4 EFA4) as WLD4.
        assert (ENV4 : lx_env m4 ss4 [] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv3 canary).
        { eapply (lx_env_heap m3 m4 ss3 ss4); [exact ENV3| rewrite E48; eapply rheap_pres_weaken; [exact HPR4| lia| auto]| exact HP4| exact MI4| exact ST4| exact ERR4| exact AUX4]. }
        apply implM_ret_bind. apply implM_ret.
        (* mv a0,s3 (= 0); jal free: free(NULL) *)
        do 2 zstep.
        eapply evt_cut; [apply FREE0; reflexivity|]. cbv beta. intros ms5 ->.
        replace (ret_pc (Z_to_bv 64 0x16154)) with (Z_to_bv 64 0x16154) by (symmetry; rpc).
        rewrite E48 in ST4.
        eapply EXIT; [exact ENV4| exact WLD4| exact FRM| cbn; lia].
    - (* calloc #1 NULL: calloc #2 still runs *)
      destruct RES as [-> HP2].
      assert (ENV2 : lx_env m2 ss2 [] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv2 canary) by (eapply lx_env_heap; [exact ENV1| exact HPR2| exact HP2| exact MI2| exact ST2| exact ERR2| exact AUX2]).
      destruct WLD2 as ((j2 & FR2) & WREST2). pose proof WREST2 as (_ & _ & _ & _ & _ & MRP2).
      rewrite E48 in ST2.
      unfold implM. iprefix. do 4 zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss2 RP msx) end.
      eapply implM_bind.
      { eapply (CALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 ss2 LB (zlength d) lo B errv2);
          rewrite ?E48; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
          [ exact HP2 | exact AUX2 | lia | exact ST2 | exact LOC | lia | exact ERR2 | exact MRP2 | exact MI2 | exact TP | reflexivity | reflexivity | lia ]. }
      cbv beta. intros r2 ss3 ms3 PO. unfold rcalloc_post in PO.
      destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & EFA3 & ESO3 & RES).
      replace (ret_pc (Z_to_bv 64 0x16118)) with (Z_to_bv 64 0x16118) by (symmetry; rpc).
      pose proof (WLD_heap LB m2 m3 ss2 ss3 (conj (ex_intro _ j2 FR2) WREST2) ltac:(rewrite E48 in HPR3; exact HPR3) ltac:(auto) ESO3 EFA3) as WLD3.
      destruct r2 as [up|].
      + (* calloc #2 gave up: free NULL, free up, exit *)
        destruct RES as (U & -> & UR & HP3 & UZ3).
        assert (ENV3 : lx_env m3 ss3 [(up, U, zlength d)] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv3 canary)
          by (eapply lx_env_heap; [exact ENV2| exact HPR3| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
        rewrite E48 in ST3.
        apply implM_ret_bind.
        (* mv s3,a0; beqz s2 (taken, to 0x16144); mv a0,s2 (= 0); jal free: free(NULL) *)
        unfold implM. iprefix.
        zstep. zstep. if_true.
        do 2 zstep.
        eapply evt_cut; [apply FREE0; reflexivity|]. cbv beta. intros ms4 ->.
        replace (ret_pc (Z_to_bv 64 0x1614c)) with (Z_to_bv 64 0x1614c) by (symmetry; rpc).
        (* mv a0,s3; jal free *)
        do 2 zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
        eapply implM_bind.
        { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 ss3 _ up U (zlength d) lo B errv3);
            rewrite ?E48; unfold RFREE_STACK;
            [ exact HP3 | left; reflexivity | exact AUX3 | lia | exact ST3 | exact LOC | lia | exact ERR3 | exact MI3 | exact TP | reflexivity ]. }
        cbv beta. intros [] ss4 ms4 PO.
        destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & EFA4 & ESO4 & HP4).
        replace (ret_pc (Z_to_bv 64 0x16154)) with (Z_to_bv 64 0x16154) by (symmetry; rpc).
        rewrite (lb_remove_head up U (zlength d) _ (HND _ _ _ HP3)) in HPR4, HP4. rewrite E48 in HPR4.
        pose proof (WLD_heap _ m3 m4 ss3 ss4 WLD3 HPR4 ltac:(auto) ESO4 EFA4) as WLD4.
        assert (ENV4 : lx_env m4 ss4 [] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv3 canary).
        { eapply (lx_env_heap m3 m4 ss3 ss4); [exact ENV3| rewrite E48; eapply rheap_pres_weaken; [exact HPR4| lia| auto]| exact HP4| exact MI4| exact ST4| exact ERR4| exact AUX4]. }
        apply implM_ret.
        eapply EXIT; [exact ENV4| exact WLD4| exact FRM| cbn; lia].
      + (* both NULL: free NULL twice, exit *)
        destruct RES as [-> HP3].
        assert (ENV3 : lx_env m3 ss3 [] LB (Z_to_bv 64 (bv_unsigned sp + -48)) tp B lo errv3 canary)
          by (eapply lx_env_heap; [exact ENV2| exact HPR3| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
        apply implM_ret_bind. apply implM_ret_bind. apply implM_ret.
        zstep. zstep. if_true.
        do 2 zstep.
        eapply evt_cut; [apply FREE0; reflexivity|]. cbv beta. intros ms4 ->.
        replace (ret_pc (Z_to_bv 64 0x1614c)) with (Z_to_bv 64 0x1614c) by (symmetry; rpc).
        do 2 zstep.
        eapply evt_cut; [apply FREE0; reflexivity|]. cbv beta. intros ms5 ->.
        replace (ret_pc (Z_to_bv 64 0x16154)) with (Z_to_bv 64 0x16154) by (symmetry; rpc).
        eapply EXIT; [exact ENV3| exact WLD3| exact FRM| cbn; lia].
  Qed.
End FZ.
End WithCeiling0.
