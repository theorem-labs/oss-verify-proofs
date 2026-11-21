(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTarget ZApiL ZHarnessL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTargetL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Driver. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Startup_glue Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Layout Exit Printf_lib Printf_stdio_iface Zlib_iface Zl_iface Driver_iface Drv_kit Zh_kit Z_dview Z_drep Z_dkit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Printf_pieces. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_zrd Z_trees_iface Z_dend Z_dinit_kit Zl_dinit9_model Zl_dreset9 Z_dendk Zl_dinit9_pieces Zl_dinit9_tail Zg_defl_pathi Zl_zrd Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Deflate. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateInitLib RefDeflSafeI5b. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import HarnessSmall HarnessLarge ZApiInst ZApiInstL DeflateTaintRel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import ZTaint ZTaintL BoundPat ZPat. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation MP := (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Monad.M PState).
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section DINIT.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HTRI : tr_init_stmt.
  Local Notation dinit_zallocH := (dinit_zalloc MALLOC).
  Local Notation dinit_env_munchH := (dinit_env_munch HBR HFRAME).
  Local Notation dinit_pres_munchH := (dinit_pres_munch HND HBR HBD).
  Local Notation buf_inH := (buf_in HBR).
  Local Notation buf_disjH := (buf_disj HND HBR HBD).
  Local Notation dinit_env_munchZH := (dinit_env_munchZ HBR HFRAME).
  Local Notation dinit_pres_munchZH := (dinit_pres_munchZ HND HBR HBD).

  Local Transparent the_zapiL.

  Theorem deflateInit9_proof : forall R : zrepsL, zrd R = zr_dL -> deflateInit9_stmt R.
  Proof.
    intros R RD. unfold deflateInit9_stmt. intros until canary. intros ENV ZS SIF LOSP SP16 FRM -> -> -> ->.
    pose proof ENV as (HP & _ & ZLS & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & TP & MI). cbn [app] in HP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    subst tp. unfold errno_addr in ERRC.
    unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK in LOSP. unfold strm_in_frame, ZS_SIZEOF in SIF.
    assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= lo).
    { intros bx Hb. pose proof (HBR _ _ _ bx HP Hb) as (_ & _ & _ & X1 & _). lia. }
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    pose proof (got_zalloc_relro _ (relro_clean_of_zl _ ZLS)) as GOT.
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (E80 : bv_unsigned (wz (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    unfold zs_pub in ZS. cbn [app] in ZS.
    destruct (zs_tail_recast m S [C8 (Zlib_iface.wz ni); C4 (Zlib_iface.wz ai); CB 4 p1; C8 (Zlib_iface.wz ti); C8 (Zlib_iface.wz no); C4 (Zlib_iface.wz ao); CB 4 p2;
                                  C8 (Zlib_iface.wz to); C8 jmsg; C8 jstate; C8 (Zlib_iface.wz 0); C8 (Zlib_iface.wz 0); C8 (Zlib_iface.wz 0)] jrest ZS) as (dt0 & p30 & adl0 & resv0 & ZS').
    clear ZS. rename ZS' into ZS. cbn [app] in ZS.
    pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    cbv [deflate_initL zl_dstate zl_dwin zl_dprev zl_dhead zl_dpend the_zapiL ZApiInstL.zinstL].
    unfold implM. iprefix. unfold Z_DEFLATEINIT_, A_ZVERSION, ZS_SIZEOF, ZApiL.Z_BEST_COMPRESSION, wint, MallocRep.wz in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 80%nat STK.
    do 10 zstep. (* 1.4 UBSan: + sd s7,8(sp) *)
    zstep. zstep. zstep. if_false.
    zstep. zstep. if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let bs := eval vm_compute in (option.default [] (image_bytes usegs 0x10415 1)) in
      assert (VER : ro_cells usegs mm 0x10415 [CB (length bs) bs])
        by (apply ro_cells_image; [assumption| vm_compute; reflexivity| lia| cbn; lia]) end.
    cbn [length] in VER.
    zstep. zstep. zstep. if_false.
    zstep. zstep. if_false.
    (* [comment removed for export] *)
    ustep 0x16754. ustep 0x16754.
    (* [comment removed for export] *)
    zs. zs. zs. if_true.
    zs. zs. zs. zs. zs. zs. if_false.
    zs. zs. zs. zs. zs. if_true.
    (* [comment removed for export] *)
    zs. if_false. zs. zs. if_true. zs. zs. zs. zs. if_false. zs. zs. if_false. zs. zs. if_false.
    zs. zs. zs. if_false. zs. zs. zs. if_false. zs. zs. zs. zs. if_false.
    zs. zs. zs. zs. zs. if_true. zs. zs. zs. zs. zs. zs. zs. zs. (* 1.4 UBSan: + mv a2,s2 *)
    clear GOT VER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENV0 : lx_env mm s [] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv canary) end.
    { eapply (lx_env_munch [(lo, bv_unsigned sp); (S, S + 112)] m _); [exact HFRAME| exact ENV| exact MU| exact WM| eassumption| rewrite E80; exact STK| rewrite E80; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor; [left; cbn [fst]; lia| constructor]].
      - intros a Ha. cbn [outside fst snd]. split; [lia| split; [lia| exact I]]. }
    assert (PR0 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mA).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; cbn [outside fst snd]; (split; [|split; [|exact I]]); try lia.
      specialize (LBR bx Hb). lia. }
    pose proof ENV0 as (HP0 & _ & _ & _ & _ & AUX0 & SPB0 & _ & STK0 & _ & _ & ERR0 & _ & MI0). cbn [app] in HP0. rewrite E80 in STK0, SPB0. unfold errno_addr in ERR0.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM usegs tm s (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
    eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mA s LB 1 5968 5968 lo B errv);
      [ exact HP0 | exact AUX0 | rewrite E80; exact SPB0 | rewrite E80; exact STK0 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR0 | exact MI0
      | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
    intros r1 st1 u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 m1 errv1 MI1 ST1 ERR1 AUX1 HPR1 EFA1 ESO1 RES1.
    rewrite E80 in ST1, HPR1.
    replace (ret_pc (wz 91508)) with (wz 91508) by (symmetry; rpc).
    assert (PR1 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m1).
    { eapply lx_pres_trans; [exact PR0|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR1| lia| intros bx Hb; exact Hb]. }
    pose proof (Drv_kit.rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ (lx_pres_of_heap_pres _ _ [] _ _ HPR1)) ZS
                  ltac:(intros a Ha; cbn in Ha; apply stack_client; [lia| cbn [rin_ivs]; tauto])) as ZS1.
    pose proof (Drv_kit.rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ (lx_pres_of_heap_pres _ _ [] _ _ HPR1)) FR
                  ltac:(intros a Ha; cbn in Ha; apply stack_client; [lia| cbn [rin_ivs]; tauto])) as FR1.
    clear ZS FR.
    destruct r1 as [ps|].
    - (* [comment removed for export] *)
      destruct RES1 as (As & jks & -> & BRs & HP1 & CBs).
      pose proof (box _ CBs) as CBX. pose proof (box _ BRs) as BRX.
      destruct BRs as (BRs1 & BRs2 & _ & BRs3 & BRs4).
      assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
      assert (ENV1 : lx_env m1 st1 [(ps, As, 5968)] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary).
      { eapply (lx_env_heap mA m1 s st1); [exact ENV0| rewrite E80; exact HPR1| exact HP1| exact MI1| rewrite E80; exact ST1| exact ERR1| exact AUX1]. }
      (* [comment removed for export] *)
      (* 1.4 UBSan: deflateInit2_ calls memset(s, 0, 5968) (zmemzero of the whole state) right after the zalloc, before any
         store into it; the recast then starts from the all-zero block jkz. *)
      unfold implM. iprefix.
      zs. zs. zs. if_false.
      zs. zs. zs. zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [eapply OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U.F_memset.memset_callZ with (D := As) (C := 0) (N := 5968); [exact CBs| eassumption| lia| lia| lia| lia] |] end.
      intros msz POSTZ. unfold OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U.F_memset.memset_postZ in POSTZ. destruct_exs POSTZ.
      destruct POSTZ as (Ez & MUz & WMz & MIz & CBzr). subst msz.
      lazymatch type of MUz with munch _ _ ?mm => rename mm into mz end.
      transport_after_call usegs m1 mz MUz WMz.
      try (replace (ret_pc (wz 91536)) with (wz 91536) by (symmetry; rpc)).
      change (0 mod 256) with 0 in CBzr.
      remember (repeat (Z_to_bv 8 0) (Z.to_nat 5968)) as jkz eqn:Ejkz.
      assert (HZz : forall k, 8 <= Z.of_nat k < 5968 -> nth k jkz (Z_to_bv 8 0) = Z_to_bv 8 0) by (intros k Hk; subst jkz; apply nth_repeat).
      rename CBzr into CBz.
      pose proof (box _ CBz) as CBXz.
      assert (MUz' : munch (WZ As) m1 mz) by (unfold WZ; exact MUz).
      assert (ENV1z : lx_env mz st1 [(ps, As, 5968)] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary)
        by (eapply (dinit_env_munchZH m1 mz); [exact ENV1| exact MUz'| exact WMz| exact MIz| left; reflexivity| lia| lia]).
      assert (PR1z : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mz).
      { destruct ENV1 as (HPx & _).
        eapply (dinit_pres_munchZH LB _ m m1 mz st1 [(ps, As, 5968)]); [exact PR1| exact MUz'| exact WMz| exact HPx| left; reflexivity| lia]. }
      clear MUz MUz' WMz. try clear CBs. try clear CBX.
      pose proof (recast_A mz As jkz 0%N dinit_cs CBz) as GA.
      pose proof (recast_D mz As jkz 0%N dinit_cs CBz HZz) as GD.
      pose proof (box _ (recast_Bi mz As jkz 0%N dinit_cs CBz)) as RBi. pose proof (box _ (recast_C mz As jkz 0%N dinit_cs CBz)) as RC.
      pose proof (recast_lt mz As jkz 0%N dinit_cs CBz) as Rlt. pose proof (recast_dt mz As jkz 0%N dinit_cs CBz) as Rdt.
      pose proof (recast_bt mz As jkz 0%N dinit_cs CBz) as Rbt. pose proof (recast_blc mz As jkz 0%N dinit_cs CBz) as Rblc.
      pose proof (recast_heap mz As jkz 0%N dinit_cs CBz) as Rheap. pose proof (recast_dep mz As jkz 0%N dinit_cs CBz) as Rdep.
      clear CBz.
      unfold dsA_raw in GA. unfold dsD_raw in GD.
      cbn [ds_of_oracle ds_status ds_pending_buf_size ds_pending ds_wrap ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask
           ds_window_size ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available
           ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match
           ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water] in GA, GD.
      pose proof (agree_on_refl (As + 212) (As + 5881) mz) as AGs.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mz) as MU1. pose proof (wmono_refl usegs mz) as WM1.
      (* [comment removed for export] *)
      ustep 0x16754. zs. ustep 0x16754.
      do 30 zs. (* 1.4 UBSan: the reordered stores, from li a2,23 to the second jalr *)
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE2 end.
      assert (ENV2 : lx_env mE2 st1 ([(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary)
        by (eapply (dinit_env_munchH mz mE2); [exact ENV1z| exact MU1| exact WM1| eassumption| left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe2 : RHEAP st1 (([(ps, As, 5968)]) ++ LB) mz) by (destruct ENV1z as (HPx & _); exact HPx).
      assert (PR2 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE2)
        by (eapply (dinit_pres_munchH LB _ m mz mE2 st1 ([(ps, As, 5968)])); [exact PR1z| exact MU1| exact WM1| exact HPe2| left; reflexivity| lia]).
      assert (AGs2 : agree_on (As + 212) (As + 5881) mz mE2)
        by (eapply (dinit_ags_munch mz mz mE2 S As); [exact AGs| exact MU1| exact WM1| lia| lia| lia]).
      pose proof ENV2 as (HPx2 & _ & _ & _ & _ & AUX2 & SPB2 & _ & STK2 & _ & _ & ERR2 & _ & MI2). rewrite E80 in STK2, SPB2. unfold errno_addr in ERR2.
      assert (HPc2 : RHEAP st1 ((ps, As, 5968) :: LB) mE2) by (exact HPx2).
      assert (INs2 : In (ps, As, 5968) ((ps, As, 5968) :: LB)) by (left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM usegs tm st1 (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE2 st1 ((ps, As, 5968) :: LB) 32768 2 65536 lo B errv1);
        [ exact HPc2 | exact AUX2 | rewrite E80; exact SPB2 | rewrite E80; exact STK2 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR2 | exact MI2
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rw st2 v20 v21 v22 d20 d21 d22 d23 d24 d25 d26 d27 v23 v24 v25 v26 mP2 errv2 MIp2 STp2 ERRp2 AUXp2 HPR2 EFA2 ESO2 RES2.
      rewrite E80 in STp2, HPR2.
      destruct (zalloc_res _ _ _ _ _ _ RES2) as (Aw & jkw & -> & HPp2 & BUFrw). clear RES2.
      assert (HPc2p : RHEAP st2 ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP2) by exact HPp2.
      replace (ret_pc (wz 91668)) with (wz 91668) by (symmetry; rpc).
      assert (ENV2p : lx_env mP2 st2 ((oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv2 canary).
      { eapply (lx_env_heap mE2 mP2 st1 st2); [exact ENV2| rewrite E80; eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc2p| exact MIp2| rewrite E80; exact STp2| exact ERRp2| exact AUXp2]. }
      assert (PR2p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP2).
      { eapply lx_pres_trans; [exact PR2|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs2p : agree_on (As + 212) (As + 5881) mz mP2).
      { eapply agree_on_trans; [exact AGs2|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR2); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs2| cbn [blk_addr blk_size fst snd]; lia]. }
      pose proof (BK_refl rw Aw mP2) as BKrw2p.
      assert (ESOs2 : ps_so st2 = ps_so s) by (rewrite ESO2; exact ESO1).
      assert (EFAs2 : ps_fa st2 = ps_fa s) by (rewrite EFA2; exact EFA1).
      tr_blk HPR2 GA GA2 (ps, As, 5968) INs2. tr_blk HPR2 GD GD2 (ps, As, 5968) INs2. tr_up HPR2 ZS1 ZS2. tr_up HPR2 FR1 FR2.
      clear GA GD ZS1 FR1.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP2) as MU2. pose proof (wmono_refl usegs mP2) as WM2.
      unfold implM. iprefix.
      do 7 zs.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE3 end.
      assert (ENV3 : lx_env mE3 st2 ((oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv2 canary)
        by (eapply (dinit_env_munchH mP2 mE3); [exact ENV2p| exact MU2| exact WM2| eassumption| apply in_or_app; left; apply in_or_app; right; left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe3 : RHEAP st2 (((oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB) mP2) by (destruct ENV2p as (HPx & _); exact HPx).
      assert (PR3 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE3)
        by (eapply (dinit_pres_munchH LB _ m mP2 mE3 st2 ((oblk rw Aw 65536) ++ [(ps, As, 5968)])); [exact PR2p| exact MU2| exact WM2| exact HPe3| apply in_or_app; right; left; reflexivity| lia]).
      assert (AGs3 : agree_on (As + 212) (As + 5881) mz mE3)
        by (eapply (dinit_ags_munch mz mP2 mE3 S As); [exact AGs2p| exact MU2| exact WM2| lia| lia| lia]).
      assert (BKrw3 : BK rw Aw _ mE3)
        by (eapply BK_munch; [exact BKrw2p| exact MU2| exact WM2| intros q E; eapply (buf_disjH st2 (oblk rw Aw 65536) LB mP2 q Aw S As ps lo); [exact HPc2p| in_ow E| lia| exact CEIL]]).
      pose proof ENV3 as (HPx3 & _ & _ & _ & _ & AUX3 & SPB3 & _ & STK3 & _ & _ & ERR3 & _ & MI3). rewrite E80 in STK3, SPB3. unfold errno_addr in ERR3.
      assert (HPc3 : RHEAP st2 ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mE3) by (rewrite <- app_assoc in HPx3; cbn [app] in HPx3; exact HPx3).
      assert (INs3 : In (ps, As, 5968) ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB)) by (apply in_or_app; right; left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM usegs tm st2 (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE3 st2 ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) 32768 2 65536 lo B errv2);
        [ exact HPc3 | exact AUX3 | rewrite E80; exact SPB3 | rewrite E80; exact STK3 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR3 | exact MI3
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rp st3 v30 v31 v32 d30 d31 d32 d33 d34 d35 d36 d37 v33 v34 v35 v36 mP3 errv3 MIp3 STp3 ERRp3 AUXp3 HPR3 EFA3 ESO3 RES3.
      rewrite E80 in STp3, HPR3.
      destruct (zalloc_res _ _ _ _ _ _ RES3) as (Ap & jkp & -> & HPp3 & BUFrp). clear RES3.
      rewrite app_assoc in HPp3.
      assert (HPc3p : RHEAP st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP3) by exact HPp3.
      replace (ret_pc (wz 91696)) with (wz 91696) by (symmetry; rpc).
      assert (ENV3p : lx_env mP3 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv3 canary).
      { eapply (lx_env_heap mE3 mP3 st2 st3); [exact ENV3| rewrite E80; eapply rheap_pres_weaken; [exact HPR3| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc3p| exact MIp3| rewrite E80; exact STp3| exact ERRp3| exact AUXp3]. }
      assert (PR3p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP3).
      { eapply lx_pres_trans; [exact PR3|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR3| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs3p : agree_on (As + 212) (As + 5881) mz mP3).
      { eapply agree_on_trans; [exact AGs3|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR3); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs3| cbn [blk_addr blk_size fst snd]; lia]. }
      assert (BKrw3p : BK rw Aw _ mP3) by (eapply BK_hpres; [exact BKrw3| exact HPR3| intros q E; eapply buf_inH; [exact HPc3| in_ow E]]).
      pose proof (BK_refl rp Ap mP3) as BKrp3p.
      assert (ESOs3 : ps_so st3 = ps_so s) by (rewrite ESO3; exact ESOs2).
      assert (EFAs3 : ps_fa st3 = ps_fa s) by (rewrite EFA3; exact EFAs2).
      tr_blk HPR3 GA2 GA3 (ps, As, 5968) INs3. tr_blk HPR3 GD2 GD3 (ps, As, 5968) INs3. tr_up HPR3 ZS2 ZS3. tr_up HPR3 FR2 FR3.
      clear GA2 GD2 ZS2 FR2.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP3) as MU3. pose proof (wmono_refl usegs mP3) as WM3.
      unfold implM. iprefix.
      do 7 zs.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE4 end.
      assert (ENV4 : lx_env mE4 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv3 canary)
        by (eapply (dinit_env_munchH mP3 mE4); [exact ENV3p| exact MU3| exact WM3| eassumption| apply in_or_app; left; apply in_or_app; right; left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe4 : RHEAP st3 (((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB) mP3) by (destruct ENV3p as (HPx & _); exact HPx).
      assert (PR4 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE4)
        by (eapply (dinit_pres_munchH LB _ m mP3 mE4 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)])); [exact PR3p| exact MU3| exact WM3| exact HPe4| apply in_or_app; right; left; reflexivity| lia]).
      assert (AGs4 : agree_on (As + 212) (As + 5881) mz mE4)
        by (eapply (dinit_ags_munch mz mP3 mE4 S As); [exact AGs3p| exact MU3| exact WM3| lia| lia| lia]).
      assert (BKrw4 : BK rw Aw _ mE4)
        by (eapply BK_munch; [exact BKrw3p| exact MU3| exact WM3| intros q E; eapply (buf_disjH st3 (oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP3 q Aw S As ps lo); [exact HPc3p| in_ow E| lia| exact CEIL]]).
      assert (BKrp4 : BK rp Ap _ mE4)
        by (eapply BK_munch; [exact BKrp3p| exact MU3| exact WM3| intros q E; eapply (buf_disjH st3 (oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP3 q Ap S As ps lo); [exact HPc3p| in_ow E| lia| exact CEIL]]).
      pose proof ENV4 as (HPx4 & _ & _ & _ & _ & AUX4 & SPB4 & _ & STK4 & _ & _ & ERR4 & _ & MI4). rewrite E80 in STK4, SPB4. unfold errno_addr in ERR4.
      assert (HPc4 : RHEAP st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mE4) by (rewrite <- app_assoc in HPx4; cbn [app] in HPx4; exact HPx4).
      assert (INs4 : In (ps, As, 5968) ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB)) by (apply in_or_app; right; left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM usegs tm st3 (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE4 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) 32768 2 65536 lo B errv3);
        [ exact HPc4 | exact AUX4 | rewrite E80; exact SPB4 | rewrite E80; exact STK4 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR4 | exact MI4
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rh st4 v40 v41 v42 d40 d41 d42 d43 d44 d45 d46 d47 v43 v44 v45 v46 mP4 errv4 MIp4 STp4 ERRp4 AUXp4 HPR4 EFA4 ESO4 RES4.
      rewrite E80 in STp4, HPR4.
      destruct (zalloc_res _ _ _ _ _ _ RES4) as (Ah & jkh & -> & HPp4 & BUFrh). clear RES4.
      rewrite app_assoc in HPp4.
      assert (HPc4p : RHEAP st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP4) by exact HPp4.
      replace (ret_pc (wz 91724)) with (wz 91724) by (symmetry; rpc).
      assert (ENV4p : lx_env mP4 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv4 canary).
      { eapply (lx_env_heap mE4 mP4 st3 st4); [exact ENV4| rewrite E80; eapply rheap_pres_weaken; [exact HPR4| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc4p| exact MIp4| rewrite E80; exact STp4| exact ERRp4| exact AUXp4]. }
      assert (PR4p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP4).
      { eapply lx_pres_trans; [exact PR4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR4| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs4p : agree_on (As + 212) (As + 5881) mz mP4).
      { eapply agree_on_trans; [exact AGs4|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR4); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs4| cbn [blk_addr blk_size fst snd]; lia]. }
      assert (BKrw4p : BK rw Aw _ mP4) by (eapply BK_hpres; [exact BKrw4| exact HPR4| intros q E; eapply buf_inH; [exact HPc4| in_ow E]]).
      assert (BKrp4p : BK rp Ap _ mP4) by (eapply BK_hpres; [exact BKrp4| exact HPR4| intros q E; eapply buf_inH; [exact HPc4| in_ow E]]).
      pose proof (BK_refl rh Ah mP4) as BKrh4p.
      assert (ESOs4 : ps_so st4 = ps_so s) by (rewrite ESO4; exact ESOs3).
      assert (EFAs4 : ps_fa st4 = ps_fa s) by (rewrite EFA4; exact EFAs3).
      tr_blk HPR4 GA3 GA4 (ps, As, 5968) INs4. tr_blk HPR4 GD3 GD4 (ps, As, 5968) INs4. tr_up HPR4 ZS3 ZS4. tr_up HPR4 FR3 FR4.
      clear GA3 GD3 ZS3 FR3.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP4) as MU4. pose proof (wmono_refl usegs mP4) as WM4.
      unfold implM. iprefix.
      do 9 zs.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE5 end.
      assert (ENV5 : lx_env mE5 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv4 canary)
        by (eapply (dinit_env_munchH mP4 mE5); [exact ENV4p| exact MU4| exact WM4| eassumption| apply in_or_app; left; apply in_or_app; right; left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe5 : RHEAP st4 (((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB) mP4) by (destruct ENV4p as (HPx & _); exact HPx).
      assert (PR5 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE5)
        by (eapply (dinit_pres_munchH LB _ m mP4 mE5 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)])); [exact PR4p| exact MU4| exact WM4| exact HPe5| apply in_or_app; right; left; reflexivity| lia]).
      assert (AGs5 : agree_on (As + 212) (As + 5881) mz mE5)
        by (eapply (dinit_ags_munch mz mP4 mE5 S As); [exact AGs4p| exact MU4| exact WM4| lia| lia| lia]).
      assert (BKrw5 : BK rw Aw _ mE5)
        by (eapply BK_munch; [exact BKrw4p| exact MU4| exact WM4| intros q E; eapply (buf_disjH st4 (oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP4 q Aw S As ps lo); [exact HPc4p| in_ow E| lia| exact CEIL]]).
      assert (BKrp5 : BK rp Ap _ mE5)
        by (eapply BK_munch; [exact BKrp4p| exact MU4| exact WM4| intros q E; eapply (buf_disjH st4 (oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP4 q Ap S As ps lo); [exact HPc4p| in_ow E| lia| exact CEIL]]).
      assert (BKrh5 : BK rh Ah _ mE5)
        by (eapply BK_munch; [exact BKrh4p| exact MU4| exact WM4| intros q E; eapply (buf_disjH st4 (oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP4 q Ah S As ps lo); [exact HPc4p| in_ow E| lia| exact CEIL]]).
      pose proof ENV5 as (HPx5 & _ & _ & _ & _ & AUX5 & SPB5 & _ & STK5 & _ & _ & ERR5 & _ & MI5). rewrite E80 in STK5, SPB5. unfold errno_addr in ERR5.
      assert (HPc5 : RHEAP st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mE5) by (rewrite <- app_assoc in HPx5; cbn [app] in HPx5; exact HPx5).
      assert (INs5 : In (ps, As, 5968) ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB)) by (apply in_or_app; right; left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM usegs tm st4 (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE5 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) 16384 4 65536 lo B errv4);
        [ exact HPc5 | exact AUX5 | rewrite E80; exact SPB5 | rewrite E80; exact STK5 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR5 | exact MI5
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rb st5 v50 v51 v52 d50 d51 d52 d53 d54 d55 d56 d57 v53 v54 v55 v56 mP5 errv5 MIp5 STp5 ERRp5 AUXp5 HPR5 EFA5 ESO5 RES5.
      rewrite E80 in STp5, HPR5.
      destruct (zalloc_res _ _ _ _ _ _ RES5) as (Ab & jkb & -> & HPp5 & BUFrb). clear RES5.
      rewrite app_assoc in HPp5.
      assert (HPc5p : RHEAP st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP5) by exact HPp5.
      replace (ret_pc (wz 91760)) with (wz 91760) by (symmetry; rpc).
      assert (ENV5p : lx_env mP5 st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary).
      { eapply (lx_env_heap mE5 mP5 st4 st5); [exact ENV5| rewrite E80; eapply rheap_pres_weaken; [exact HPR5| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc5p| exact MIp5| rewrite E80; exact STp5| exact ERRp5| exact AUXp5]. }
      assert (PR5p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP5).
      { eapply lx_pres_trans; [exact PR5|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR5| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs5p : agree_on (As + 212) (As + 5881) mz mP5).
      { eapply agree_on_trans; [exact AGs5|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR5); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs5| cbn [blk_addr blk_size fst snd]; lia]. }
      assert (BKrw5p : BK rw Aw _ mP5) by (eapply BK_hpres; [exact BKrw5| exact HPR5| intros q E; eapply buf_inH; [exact HPc5| in_ow E]]).
      assert (BKrp5p : BK rp Ap _ mP5) by (eapply BK_hpres; [exact BKrp5| exact HPR5| intros q E; eapply buf_inH; [exact HPc5| in_ow E]]).
      assert (BKrh5p : BK rh Ah _ mP5) by (eapply BK_hpres; [exact BKrh5| exact HPR5| intros q E; eapply buf_inH; [exact HPc5| in_ow E]]).
      pose proof (BK_refl rb Ab mP5) as BKrb5p.
      assert (ESOs5 : ps_so st5 = ps_so s) by (rewrite ESO5; exact ESOs4).
      assert (EFAs5 : ps_fa st5 = ps_fa s) by (rewrite EFA5; exact EFAs4).
      tr_blk HPR5 GA4 GA5 (ps, As, 5968) INs5. tr_blk HPR5 GD4 GD5 (ps, As, 5968) INs5. tr_up HPR5 ZS4 ZS5. tr_up HPR5 FR4 FR5.
      clear GA4 GD4 ZS4 FR4.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP5) as MU5. pose proof (wmono_refl usegs mP5) as WM5.
      (* [comment removed for export] *)
      (* 1.4 UBSan: gzhead is no longer stored (sd zero,56(s1) is gone); the memset left it 0 *)
      assert (EGZ : jw jkz 56 = wz 0) by (apply jw_zero; [lia| intros k Hk; apply HZz; lia]).
      rewrite EGZ in GA5.
      eapply (dinit9_tail FREE HND HBR HBD HFRAME HTRI R RD ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB S ni ai ti no ao to p1 p2 lo B canary
                ps As jkz mz rw rp rh rb Aw Ap Ah Ab jkw jkp jkh jkb mP2 mP3 mP4 mP5 st5 errv5 dt0 p30 adl0 resv0 _);
        [ exact SIF | exact LOSP | exact SP16 | exact FRM | exact ENV5p | exact PR5p | exact ESOs5 | exact EFAs5 | exact (unbox _ CBXz) | exact (unbox _ BRX) | exact AGs5p
        | exact BKrw5p | exact BKrp5p | exact BKrh5p | exact BUFrw | exact BUFrp | exact BUFrh | exact BUFrb | exact GA5 | exact GD5 | exact ZS5 | exact FR5 ].
    - (* [comment removed for export] *)
      destruct RES1 as (-> & HP1).
      assert (ENV1 : lx_env m1 st1 [] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary).
      { eapply (lx_env_heap mA m1 s st1); [exact ENV0| rewrite E80; exact HPR1| exact HP1| exact MI1| rewrite E80; exact ST1| exact ERR1| exact AUX1]. }
      cbn [ret lops Target.ops]. apply implM_ret.
      pose proof (munch_refl [] m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
      zs. zs. zs. if_true.
      zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. (* 1.4 UBSan: + ld s7 *)
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evt_done. unfold deflateInit9_post. do 15 eexists. exists F, fc, m1.
      split; [reflexivity|]. cbv beta iota.
      split; [|split; [unfold wint, ZApi.Z_MEM_ERROR, MallocRep.wz; apply bv_eq; reflexivity|]].
      + unfold lx_post_env. split; [exists errv1; eapply lx_env_sp; [exact ENV1| exact ST1| lia]|]. split; [exact FRM|].
        split; [exact PR1| split; [exact ESO1| exact EFA1]].
      + destruct (rw_cells_forget usegs m1 _ _ ZS1) as (j & Hj). exists j. exact Hj.
  Qed.
End DINIT.
End WithCeiling0.
