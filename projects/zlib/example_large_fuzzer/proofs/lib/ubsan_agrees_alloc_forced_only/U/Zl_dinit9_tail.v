(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget ZApiL ZHarnessL ZInstL ZTargetL Target Driver Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Startup_glue Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Layout Exit Printf_lib Printf_stdio_iface Zlib_iface Zl_iface Driver_iface Drv_kit Zh_kit Z_dview Z_drep Z_dkit Printf_pieces Z_zrd Z_trees_iface Z_dend Z_dinit_kit Zl_dinit9_model Zl_dreset9 Z_dendk Zl_dinit9_pieces Zg_defl_pathi Zl_dparams_pathi Zl_zrd Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Deflate RefDeflateInitLib RefDeflSafeI5b HarnessSmall HarnessLarge ZApiInst ZApiInstL ZApiOk DeflateTaintRel ZTaint ZTaintL BoundPat ZPat FillWinModel DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import StoreFast.
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

Section DINIT_TAIL.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HTRI : tr_init_stmt.
  Local Notation dinit_failH := (dinit_fail FREE HND HBR HBD HFRAME).
  Local Notation dinit_env_munchH := (dinit_env_munch HBR HFRAME).
  Local Notation dinit_pres_munchH := (dinit_pres_munch HND HBR HBD).
  Local Notation buf_inH := (buf_in HBR).
  Local Notation buf_disjH := (buf_disj HND HBR HBD).
  Local Notation "x ;;- k" := (bind lops x (fun _ => k)) (at level 62, right associativity).
  Local Transparent the_zapiL.

  (* [comment removed for export] *)
  Definition sx5 (jks : list byte) : deflate_state := s_lbs (s_setup (orc jks) 0%N dinit_cs 1 15 8) 8.

  (* [comment removed for export] *)
  Definition G5 (jks jkw jkp jkh jkb : list byte) (k : N) : Z -> Z :=
    match k with 0%N => orc jks | 1%N => orc jkw | 2%N => orc jkp | 3%N => orc jkh | _ => orc jkb end.

  (* [comment removed for export] *)
  Lemma dinit9_tail : forall (R : zrepsL), zrd R = zr_dL ->
    forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LB : list block) (S ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (canary : word)
         (ps : bptr) (As : Z) (jks : list byte) (m1 : mem)
         (rw rp rh rb : option bptr) (Aw Ap Ah Ab : Z) (jkw jkp jkh jkb : list byte) (mP2 mP3 mP4 mP5 : mem) (st5 : PState) (errv5 : word)
         (dt0 : word) (p30 : list byte) (adl0 resv0 : word) (fj : list byte)
         (ra0 v50 v51 v52 d51 d52 d53 d54 d55 d56 d57 v53 v54 v55 v56 v57 : word),
    strm_in_frame sp S B -> lo <= bv_unsigned sp - Z_DEFLATEINIT_STACK -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
    lx_env mP5 st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB
           (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary ->
    lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP5 -> ps_so st5 = ps_so s -> ps_fa st5 = ps_fa s ->
    rw_cells usegs m1 As [CB (Z.to_nat 5968) jks] -> rblock_range As 5968 ->
    agree_on (As + 212) (As + 5881) m1 mP5 ->
    BK rw Aw mP2 mP5 -> BK rp Ap mP3 mP5 -> BK rh Ah mP4 mP5 ->
    (forall p, rw = Some p -> rblock_range Aw 65536 /\ rw_cells usegs mP2 Aw [CB (Z.to_nat 65536) jkw]) ->
    (forall p, rp = Some p -> rblock_range Ap 65536 /\ rw_cells usegs mP3 Ap [CB (Z.to_nat 65536) jkp]) ->
    (forall p, rh = Some p -> rblock_range Ah 65536 /\ rw_cells usegs mP4 Ah [CB (Z.to_nat 65536) jkh]) ->
    (forall p, rb = Some p -> rblock_range Ab 65536 /\ rw_cells usegs mP5 Ab [CB (Z.to_nat 65536) jkb]) ->
    rw_cells usegs mP5 As (dsA_raw (wz S) (jw jks 16) (jw jks 32) (wz 0) (wz (oadr rw Aw)) (wz (oadr rp Ap)) (wz (oadr rh Ah)) (sx5 jks)
                                   (jp jks 12 4) (jp jks 52 4) (jp jks 73 3) (jp jks 92 4) (jp jks 148 4)) ->
    rw_cells usegs mP5 (As + 5881) (dsD_raw (jw jks 5888) (sx5 jks) (jp jks 5881 7) (jp jks 5908 4) (jp jks 5938 2) (jp jks 5944 4) (jp jks 5960 4)) ->
    rw_cells usegs mP5 S (zs_raw As ni ai ti no ao to p1 p2 (wz 0) (wz 0) dt0 p30 adl0 resv0) ->
    rw_cells usegs mP5 (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    implM usegs
      (match rw, rp, rh, rb with
       | Some wp, Some pp, Some hp, Some bp => ret lops (Some (ps, wp, pp, hp, bp))
       | _, _, _, _ => lib_free lops rb ;;- lib_free lops rh ;;- lib_free lops rp ;;- lib_free lops rw ;;- lib_free lops (Some ps) ;;- ret lops None
       end) st5
      (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
      (MS (mkR ra0 (wz (bv_unsigned sp + -80)) gp (wz RATP) v50 v51 v52 (wz S) (wz As) (wz (oadr rb Ab)) d51 d52 d53 d54 d55 d56 d57
               (wz (As + 5888)) (wz 0) (wz 9) (wz 1) (wz 8) v57 s8 s9 s10 s11 v53 v54 v55 v56)
          F (wz 0x16670) fc None mP5 (seg_rom usegs)).
  Proof.
    intros R RD. intros until v57. intros SIF LOSP SP16 FRM ENV5 PR5 ESO5 EFA5 CBs BRs AGs5 BKw BKp BKh BUFw BUFp BUFh BUFb GA GD ZS FR.
    pose proof ENV5 as (HP5 & _ & ZLS & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & _ & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof SIF as SIF'. unfold strm_in_frame, ZS_SIZEOF in SIF'. pose proof LOSP as LOSP'. unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK in LOSP'.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    assert (E80 : bv_unsigned (wz (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    rewrite E80 in STK, SPB.
    destruct BRs as (BRs1 & BRs2 & _ & BRs3 & BRs4).
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    assert (INs : In (ps, As, 5968) (((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. unfold dsA_raw, sx5 in GA. unfold dsD_raw, sx5 in GD.
    cbn [s_lbs s_setup set_status set_wrap set_gzhead set_w_bits set_w_size set_w_mask set_hash_bits set_hash_size set_hash_mask set_hash_shift set_high_water set_lit_bufsize
         ds_of_oracle ds_status ds_pending_buf_size ds_pending ds_wrap ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask
         ds_window_size ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available
         ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match
         ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water] in GA, GD.
    change (Z.shiftl 1 15) with 32768 in GA. change (Z.shiftl 1 (8 + 7)) with 32768 in GA. change (8 + 7) with 15 in GA.
    change ((15 + MIN_MATCH - 1) / MIN_MATCH) with 5 in GA. change (32768 - 1) with 32767 in GA. change (Z.shiftl 1 (8 + 6)) with 16384 in GD.
    unfold MallocRep.wz, Z_ZCALLOC, Z_ZCFREE in ZS.
    pose proof (munch_refl (WI S As) mP5) as MU5. pose proof (wmono_refl usegs mP5) as WM5. unfold WI in MU5.
    unfold implM. iprefix.
    zs. zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mF end.
    assert (MIF : mem_inv usegs mF) by eassumption.
    assert (ENVF : lx_env mF st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB
                          (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary)
      by (eapply (dinit_env_munchH mP5 mF); [exact ENV5| exact MU5| exact WM5| exact MIF| exact INs| rewrite E80; lia| lia| lia| lia]).
    assert (PRF : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mF)
      by (eapply (dinit_pres_munchH LB _ m mP5 mF st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]));
          [exact PR5| exact MU5| exact WM5| exact HP5| apply in_or_app; right; left; reflexivity| lia]).
    assert (FAILK : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' v18 v19 v20 v21 v22 v23 t3' t4' t5' t6' : word),
      implM usegs (lib_free lops rb ;;- lib_free lops rh ;;- lib_free lops rp ;;- lib_free lops rw ;;- lib_free lops (Some ps) ;;- ret lops None) st5
        (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra' (wz (bv_unsigned sp + -80)) gp (wz RATP) t0' t1' t2' (wz S) (wz As) a0' a1' a2' a3' a4' a5' a6' a7' v18 v19 v20 v21 v22 v23 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz 0x166fc) fc None mF (seg_rom usegs))).
    { intros. eapply (dinit_failH R ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB S As ps lo B canary ni ai ti no ao to p1 p2
                        rb rh rp rw Ab Ah Ap Aw st5 mF errv5 (wz 0) dt0 p30 adl0 resv0 (jw jks 32) (wz 0) (set_pending_buf_size (sx5 jks) 65536));
        [ exact SIF | exact LOSP | exact FRM | exact ENVF | exact PRF | exact ESO5 | exact EFA5 | exact ZS | exact GA | exact FR ]. }
    (* [comment removed for export] *)
    zs. destruct rw as [pw|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFw pw eq_refl) as ((BRw1 & BRw2 & _ & BRw3 & BRw4) & CBw). clear BUFw.
    assert (EUw : bv_unsigned (wz Aw) = Aw) by (apply unsigned_lit; lia).
    if_false.
    (* [comment removed for export] *)
    zs. zs. destruct rp as [pp|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFp pp eq_refl) as ((BRp1 & BRp2 & _ & BRp3 & BRp4) & CBp). clear BUFp.
    assert (EUp : bv_unsigned (wz Ap) = Ap) by (apply unsigned_lit; lia).
    if_false.
    (* [comment removed for export] *)
    zs. zs. destruct rh as [ph|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFh ph eq_refl) as ((BRh1 & BRh2 & _ & BRh3 & BRh4) & CBh). clear BUFh.
    assert (EUh : bv_unsigned (wz Ah) = Ah) by (apply unsigned_lit; lia).
    if_false.
    (* [comment removed for export] *)
    zs. destruct rb as [pb|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFb pb eq_refl) as ((BRb1 & BRb2 & _ & BRb3 & BRb4) & CBb). clear BUFb.
    assert (EUb : bv_unsigned (wz Ab) = Ab) by (apply unsigned_lit; lia).
    if_false.
    clear FAILK.
    (* [comment removed for export] *)
    zs. ustep 0x16754.
    (* [comment removed for export] *)
    do 9 zs.
    zstep. replace (le1 (wz 8)) with [Z_to_bv 8 8] by (vm_compute; reflexivity). mem_after_store.
    zs.
    do 9 zs. zs. zs.
    release_frame FR STK (bv_unsigned sp).
    cbn [oadr] in GA.
    cbn [oblk app] in HP5.
    (* [comment removed for export] *)
    assert (SEP : apart As 5968 Aw 65536 /\ apart As 5968 Ap 65536 /\ apart As 5968 Ah 65536 /\ apart As 5968 Ab 65536
                  /\ apart Aw 65536 Ap 65536 /\ apart Aw 65536 Ah 65536 /\ apart Aw 65536 Ab 65536
                  /\ apart Ap 65536 Ah 65536 /\ apart Ap 65536 Ab 65536 /\ apart Ah 65536 Ab 65536).
    { unfold apart.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536)]) I2 => heap_sep st5 [(pb, Ab, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X1.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536); (ph, Ah, 65536)]) I2 => heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X2.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536)]) I2 =>
                    heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X3.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536)]) I2 =>
                    heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X4.
      pose proof (X1 _ (ph, Ah, 65536) (or_introl eq_refl) (or_introl eq_refl)) as Y1.
      pose proof (X1 _ (pp, Ap, 65536) (or_introl eq_refl) (or_intror (or_introl eq_refl))) as Y2.
      pose proof (X1 _ (pw, Aw, 65536) (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl)))) as Y3.
      pose proof (X1 _ (ps, As, 5968) (or_introl eq_refl) (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Y4.
      pose proof (X2 (ph, Ah, 65536) (pp, Ap, 65536) (or_intror (or_introl eq_refl)) (or_introl eq_refl)) as Y5.
      pose proof (X2 (ph, Ah, 65536) (pw, Aw, 65536) (or_intror (or_introl eq_refl)) (or_intror (or_introl eq_refl))) as Y6.
      pose proof (X2 (ph, Ah, 65536) (ps, As, 5968) (or_intror (or_introl eq_refl)) (or_intror (or_intror (or_introl eq_refl)))) as Y7.
      pose proof (X3 (pp, Ap, 65536) (pw, Aw, 65536) (or_intror (or_intror (or_introl eq_refl))) (or_introl eq_refl)) as Y8.
      pose proof (X3 (pp, Ap, 65536) (ps, As, 5968) (or_intror (or_intror (or_introl eq_refl))) (or_intror (or_introl eq_refl))) as Y9.
      pose proof (X4 (pw, Aw, 65536) (ps, As, 5968) (or_intror (or_intror (or_intror (or_introl eq_refl)))) (or_introl eq_refl)) as Y10.
      cbn [blk_addr blk_size fst snd] in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10. clear - Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10. lia. }
    destruct SEP as (Qsw & Qsp & Qsh & Qsb & Qwp & Qwh & Qwb & Qph & Qpb & Qhb).
    (* [comment removed for export] *)
    assert (LAY : dlay_ok (U.Z_drep.mkDL S As Aw Ap Ah Ab 0 0)).
    { constructor; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab].
      - unfold blk_ok. clear - BRs1 BRs2 BRs3 BRs4. lia.
      - unfold blk_ok. clear - BRw1 BRw2 BRw3 BRw4. lia.
      - unfold blk_ok. clear - BRp1 BRp2 BRp3 BRp4. lia.
      - unfold blk_ok. clear - BRh1 BRh2 BRh3 BRh4. lia.
      - unfold blk_ok. clear - BRb1 BRb2 BRb3 BRb4. lia.
      - clear - SIF' B63 RSP LOSP' CEIL. lia.
      - exact Qsw. - exact Qsp. - exact Qsh. - exact Qsb. - exact Qwp. - exact Qwh. - exact Qwb. - exact Qph. - exact Qpb. - exact Qhb.
      - unfold apart. clear - SIF' LOSP' CEIL BRs3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRw3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRp3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRh3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRb3. lia. }
    remember (U.Z_drep.mkDL S As Aw Ap Ah Ab 0 0) as L eqn:EL.
    (* [comment removed for export] *)
    assert (ENVJ : lx_env m0 st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB
                          (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary).
    { eapply (dinit_env_munchH mP5 m0); [exact ENV5| unfold WI; exact MU5| exact WM5| exact MIF| exact INs| rewrite E80; lia| lia| lia| lia]. }
    assert (PRJ : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m0).
    { eapply (dinit_pres_munchH LB _ m mP5 m0 st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)]);
        [exact PR5| unfold WI; exact MU5| exact WM5| exact HP5| right; right; right; right; left; reflexivity| lia]. }
    pose proof ENVJ as (_ & _ & ZLSJ & _). pose proof (relro_clean_of_zl _ ZLSJ) as RCJ.
    (* [comment removed for export] *)
    assert (AGJ : agree_on (As + 212) (As + 5881) m1 m0)
      by (eapply (dinit_ags_munch m1 mP5 m0 S As); [exact AGs5| unfold WI; exact MU5| exact WM5| lia| lia| lia]).
    assert (AGw : agree_on Aw (Aw + 65536) mP2 m0).
    { eapply agree_on_trans; [exact (BKw pw eq_refl)|]. apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsw SIF' LOSP' CEIL BRw3 RSP. unfold apart in Qsw. lia. }
    assert (AGp : agree_on Ap (Ap + 65536) mP3 m0).
    { eapply agree_on_trans; [exact (BKp pp eq_refl)|]. apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsp SIF' LOSP' CEIL BRp3 RSP. unfold apart in Qsp. lia. }
    assert (AGh : agree_on Ah (Ah + 65536) mP4 m0).
    { eapply agree_on_trans; [exact (BKh ph eq_refl)|]. apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsh SIF' LOSP' CEIL BRh3 RSP. unfold apart in Qsh. lia. }
    assert (AGb : agree_on Ab (Ab + 65536) mP5 m0).
    { apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsb SIF' LOSP' CEIL BRb3 RSP. unfold apart in Qsb. lia. }
    (* [comment removed for export] *)
    remember (init_u64 (orc jks) 32 0 - Ab) as po eqn:Epo.
    assert (ST : DSTi m0 L (spre9 (G5 jks jkw jkp jkh jkb) po)).
    { pose proof (recast_Bi m1 As jks 0%N dinit_cs CBs) as GB. pose proof (recast_C m1 As jks 0%N dinit_cs CBs) as GC.
      pose proof (recast_lt m1 As jks 0%N dinit_cs CBs) as Glt. pose proof (recast_dt m1 As jks 0%N dinit_cs CBs) as Gdt.
      pose proof (recast_bt m1 As jks 0%N dinit_cs CBs) as Gbt. pose proof (recast_blc m1 As jks 0%N dinit_cs CBs) as Gblc.
      pose proof (recast_heap m1 As jks 0%N dinit_cs CBs) as Gheap. pose proof (recast_dep m1 As jks 0%N dinit_cs CBs) as Gdep.
      change (Z.to_nat 65536) with (Z.to_nat (2 * 32768)) in CBp, CBh.
      pose proof (recast_bytes mP2 Aw jkw 65536 CBw ltac:(lia)) as Gwin. pose proof (recast_ush mP3 Ap jkp 32768 CBp ltac:(lia)) as Gprev.
      pose proof (recast_ush mP4 Ah jkh 32768 CBh ltac:(lia)) as Ghead. pose proof (recast_bytes mP5 Ab jkb 65536 CBb ltac:(lia)) as Gpend.
      unfold jw in GA. subst L. constructor.
      - abstract (do 5 eexists; rewrite spre9_A_cells; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab G5]; close_cells GA).
      - abstract (do 9 eexists; rewrite spre9_Bi_cells; unfold s_raw9; cbn [dl_As G5]; eapply (U.Z_dview.rw_cells_agree m1 m0); [exact GB| lazymatch goal with |- agree_on _ (_ + Z.of_nat ?n) _ _ => replace (Z.of_nat n) with 72 by reflexivity end; eapply agree_on_sub; [exact AGJ| lia| lia]]).
      - abstract (unfold dsC; rewrite spre9_C_cells; unfold s_raw9; cbn [dl_As G5]; eapply (U.Z_dview.rw_cells_agree m1 m0); [exact GC| lazymatch goal with |- agree_on _ (_ + Z.of_nat ?n) _ _ => replace (Z.of_nat n) with 8 by reflexivity end; eapply agree_on_sub; [exact AGJ| lia| lia]]).
      - abstract (do 5 eexists; rewrite spre9_D_cells; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab G5]; close_cells GD).
      - abstract (apply spre9_lt; unfold s_raw9; cbn [G5]; apply (dlt_agree m1 m0 _ _ Glt); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre9_dt; unfold s_raw9; cbn [G5]; apply (ddt_agree m1 m0 _ _ Gdt); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre9_bt; unfold s_raw9; cbn [G5]; apply (dbt_agree m1 m0 _ _ Gbt); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre9_blc; unfold s_raw9; cbn [G5]; apply (dblc_agree m1 m0 _ _ Gblc); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre9_heap; unfold s_raw9; cbn [G5]; apply (dheap_agree m1 m0 _ _ Gheap); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre9_dep; unfold s_raw9; cbn [G5]; apply (ddep_agree m1 m0 _ _ Gdep); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre9_win; cbn [dl_Aw G5]; eapply (U.Z_dview.u8arr_agree mP2 m0); [exact Gwin| rewrite av8_length; change (Z.of_nat (Z.to_nat 65536)) with 65536; exact AGw]).
      - abstract (apply spre9_prev; cbn [dl_Ap G5]; eapply (U.Z_dview.u16arr_agree mP3 m0); [exact Gprev| rewrite av16_length; change (2 * Z.of_nat (Z.to_nat 32768)) with 65536; exact AGp]).
      - abstract (apply spre9_head; cbn [dl_Ah G5]; eapply (U.Z_dview.u16arr_agree mP4 m0); [exact Ghead| rewrite av16_length; change (2 * Z.of_nat (Z.to_nat 32768)) with 65536; exact AGh]).
      - abstract (apply spre9_pend; cbn [dl_Ab G5]; eapply (U.Z_dview.u8arr_agree mP5 m0); [exact Gpend| rewrite av8_length; change (Z.of_nat (Z.to_nat 65536)) with 65536; exact AGb]).
      - exact (spre9_lens _ _).
      - exact LAY. }
    destruct (spre9_facts (G5 jks jkw jkp jkh jkb) po) as (Fchk & Fwrap & Flev & Fws & Fhs).
    eapply evt_mono.
    { eapply (deflateReset9_spec HTRI L (spre9 (G5 jks jkw jkp jkh jkb) po) ni ai ti no ao to p1 p2 (wz 0) (wz 0) dt0 p30 adl0 resv0 lo).
      - exact ST.
      - subst L. unfold zs_raw, zs_pub. cbn [app dl_S dl_As]. exact ZS.
      - exact RCJ.
      - exact Fchk.
      - rewrite Fwrap. lia.
      - exact Flev. - exact Fws. - exact Fhs. - reflexivity.
      - exact STK.
      - subst L. unfold dlay_below. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab]. clear - SIF' LOSP' CEIL GLO' BRs3 BRw3 BRp3 BRh3 BRb3. lia.
      - unfold Z_DRESET_STACK. clear - LOSP'. lia.
      - exact MIF.
      - subst L. reflexivity. }
    intros ms' POST. cbv beta.
    destruct POST as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & STK' & EA0 & ZS' & ST').
    rewrite dinit9_state_eq in ST'.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM usegs tm st5 (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
    cbn [ret lops Target.ops]. apply implM_ret. apply evt_done.
    unfold deflateInit9_post. do 15 eexists. exists F, fc, m'.
    split; [reflexivity|]. cbv beta iota.
    exists As, Aw, Ap, Ah, Ab.
    subst L. cbn [dl_S dl_As dl_Ah] in MU'. cbn [dl_S dl_As] in ZS'.
    (* [comment removed for export] *)
    assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= lo
                                    /\ (blk_addr bx + blk_size bx <= As \/ As + 5968 <= blk_addr bx) /\ (blk_addr bx + blk_size bx <= Ah \/ Ah + 65536 <= blk_addr bx)).
    { intros bx Hb. pose proof (HBR _ _ _ bx HP5 ltac:(do 5 right; exact Hb)) as (_ & _ & _ & X1 & _).
      pose proof (heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB mP5 (ps, As, 5968) bx HND HBD HP5
                    ltac:(do 4 right; left; reflexivity) Hb) as X2.
      pose proof (heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB mP5 (ph, Ah, 65536) bx HND HBD HP5
                    ltac:(right; left; reflexivity) Hb) as X3.
      cbn [blk_addr blk_size fst snd] in X2, X3. clear - X1 X2 X3 CEIL. lia. }
    (* [comment removed for export] *)
    assert (ENVE : lx_env m' st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB sp (wz RATP) B lo errv5 canary).
    { eapply (lx_env_munch _ m0 m'); [exact HFRAME| exact ENVJ| exact MU'| exact WM'| exact MI'| exact STK'| clear - SIF'; lia| |].
      - constructor; [left; cbn [fst]; clear - CEIL; lia|].
        constructor; [left; cbn [fst]; clear - CEIL SIF' LOSP'; lia|].
        constructor; [right; right; exists (ps, As, 5968); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
        constructor; [right; right; exists (ph, Ah, 65536); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| constructor].
      - intros a Ha. cbn [outside fst snd]. clear - Ha SIF' LOSP' CEIL GLO' BRs3 BRh3 BRs4 BRh4 B63 RSP.
        split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]. }
    split.
    { unfold lx_post_env. split; [exists errv5; exact ENVE|]. split; [exact FRM|]. split; [| split; [exact ESO5| exact EFA5]].
      eapply lx_pres_trans; [exact PRJ|]. eapply lx_pres_of_munch; [exact MU'| exact WM'|].
      intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; unfold ZS_SIZEOF in NX; cbn [outside fst snd].
      - clear - NX Ha SIF' LOSP' CEIL BRs3 BRh3. split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]].
      - destruct (LBR bx Hb) as (Y1 & Y2 & Y3). clear - NX Hr Y1 Y2 Y3 SIF' LOSP' CEIL. split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]].
      - clear - NX Ha GLO' SIF' LOSP' CEIL BRs4 BRh4. split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]. }
    split; [rewrite EA0; unfold wint, ZApi.Z_OK, MallocRep.wz; apply bv_eq; reflexivity|].
    unfold zs_raw in ZS'. apply Startup_glue.rw_cells_app in ZS'. destruct ZS' as [ZP ZQ].
    destruct dz9_init_scalars as (Em & Edt & Ead & Et1 & Et2).
    unfold dsl_tin, dsl_tout. cbn [dl_init9 the_zapiL ZApiInstL.zinstL]. rewrite Et1, Et2.
    split; [exact ZP|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite RD.
    change (zr_dL m' (dl_S (U.Z_drep.mkDL S As Aw Ap Ah Ab 0 0)) (zd_blocks (ps, pw, pp, ph, pb) (U.Z_drep.mkDL S As Aw Ap Ah Ab 0 0)) zdl_init9).
    apply (zr_dL_intro m' _ (dinit9_of (G5 jks jkw jkp jkh jkb)) _ zdl_init9).
    - split; [| exact ST']. unfold dzq. rewrite Em, Edt, Ead. exists p30, resv0.
      unfold zs_priv_cells. cbn [dl_S dl_As].
      lazymatch type of ZQ with rw_cells _ _ (_ + Z.of_nat ?n) _ => replace (Z.of_nat n) with 48 in ZQ by reflexivity end.
      close_cells ZQ.
    - apply DRELL_init9.
    - apply PATG_init9.
    - unfold dlay_ceil. cbn [dl_As dl_Aw dl_Ap dl_Ah dl_Ab]. clear - BRs3 BRw3 BRp3 BRh3 BRb3. lia.
    - unfold zstrm_okP. rewrite Edt, Ead, Et1, Et2. clear. lia.
  Qed.
End DINIT_TAIL.
End WithCeiling0.
