(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_ukit Z_adler32 Zg_adler32_iface Zg_readbuf Zg_defl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6 RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FILL.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmtg.

Lemma slow_fillg : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_ok 32768 32768 X flush -> 0 <= flush <= 5 ->
  ds_wrap X <> 2 -> cs_avail_in (ds_strm X) < 2^31 -> din_tie inp X ->
  - 2 ^ 62 <= ds_block_start X < 2 ^ 62 ->
  (forall X1, st_fill X flush = (X1, Some (LRet need_more)) -> SKret L flush rest0 lo r fj F fc me Q 0 X1) ->
  (forall X1, st_fill X flush = (X1, Some LBreak) -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_TAIL X1) ->
  (forall X1, st_fill X flush = (X1, None) -> 3 <= ds_lookahead X1 -> KH L flush rest0 lo r fj F fc me Q X1) ->
  (forall X1, st_fill X flush = (X1, None) -> ds_lookahead X1 < 3 -> KD L flush rest0 lo r fj F fc me Q (prev_st X1)) ->
  evt usegs Q (MS (slowR L flush r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (wz Z_SLOW_HEAD) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) (RLA & FWOK & RLA1 & HOK) HFL WRAP AIN TIE RBS KRET KBRK KHASH KLO.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR, Z_SLOW_HEAD. unfold slow_frame in FR. unfold slow_W in MU. unfold KH, SK, Z_SLOW_HASH in KHASH. unfold KD, Z_SLOW_DECIDE in KLO.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  change MIN_LOOKAHEAD with 262 in *. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  zs. zstep.
  if_cases KLA; zify_cond KLA; rewrite ?unsigned_lit in KLA by lia.
  - (* [comment removed for export] *)
    assert (EF : st_fill X flush = (X, None)).
    { unfold st_fill. change MIN_LOOKAHEAD with 262. replace (ds_lookahead X <? 262) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    unfold slowR in KHASH. eapply (KHASH X EF ltac:(lia)).
    split; [exact DR0|]. split; [exact DOUT|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  - (* [comment removed for export] *)
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
    pose proof (fill_window_keep X) as KEEP. unfold fw_keep in KEEP.
    assert (EO : cs_out_rev (ds_strm (fill_window X)) = cs_out_rev (ds_strm X)) by (decompose [and] KEEP; assumption).
    clear KEEP.
    pose proof (unbox _ ROOM) as OL0.
    unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X) OL0) as OL.
    clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
    zstep. zstep.
    call (HFW L X inp (Z.of_nat (length rest0)) lo).
    1:{ exact DR0. } 1:{ apply (slow_din L inp rest0 lo r me CTX). unfold slow_W. exact MU. } 1:{ exact TIE. } 1:{ exact MI. }
    1:{ rewrite ESP. exact STK. } 1:{ unfold Z_FILLWIN_STACKG, Z_FILLWIN_STACK. rewrite ESP. lia. } 1:{ rewrite ESP. pose proof (unbox _ SP16). clear - H RSP LOsp. Z.div_mod_to_equations. lia. }
    1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. } 1:{ apply FWOK. lia. } 1:{ exact WRAP. } 1:{ exact AIN. } 1:{ exact RBS. } 1:{ reflexivity. }
    name_mem mA.
    lazymatch goal with H : stk usegs mA lo _ |- _ => rewrite ?ESP in H; rename H into STK1 end.
    lazymatch goal with H : DREP _ _ (fill_window X) |- _ => rename H into DR1 end.
    lazymatch goal with H : mem_inv usegs mA |- _ => rename H into MI1 end.
    assert (SI1 : SINV L flush rest0 lo r fj me (fill_window X) mA).
    { split; [exact DR1|]. split; [unfold dout, outv; rewrite EO; exact DOUT|]. split; [rewrite EO; exact ROOM|].
      split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| exact MI1]. }
    remember (fill_window X) as X1 eqn:EX1.
    assert (EFm : st_fill X flush = (X1, if (ds_lookahead X1 <? 262) && (flush =? Z_NO_FLUSH) then Some (LRet need_more)
                                        else if ds_lookahead X1 =? 0 then Some LBreak else None)).
    { unfold st_fill. change MIN_LOOKAHEAD with 262. replace (ds_lookahead X <? 262) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite <- EX1. destruct (_ && _); [reflexivity|]. destruct (_ =? 0); reflexivity. }
    rewrite EFm in RLA1. cbn [fst] in RLA1.
    destruct DR1 as [ZS ST]. open_DST ST. open_A GA.
    clear DR0 DOUT OL OL0 EO.
    zs.
    unfold Z_NO_FLUSH, Z_FINISH in *.
    (* [comment removed for export] *)
    assert (CONT : (ds_lookahead X1 <? 262) && (flush =? 0) = false ->
      forall a1 a5 a6 a7 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31,
      evt usegs Q (MS (slowR L flush r a1 a5 a6 a7 (wz (ds_lookahead X1)) a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31)
          F (wz 0x1a154) fc None mA (seg_rom usegs))).
    { intros EC. intros. unfold slowR. rewrite EC in EFm.
      zstep. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
      - (* [comment removed for export] *)
        replace (ds_lookahead X1 =? 0) with true in EFm by (symmetry; apply Z.eqb_eq; lia).
        unfold SK in KBRK. eapply (KBRK X1 EFm). exact SI1.
      - replace (ds_lookahead X1 =? 0) with false in EFm by (symmetry; apply Z.eqb_neq; lia).
        (* [comment removed for export] *)
        assert (Hsnd : snd (st_fill X flush) = None) by (rewrite EFm; reflexivity).
        pose proof (proj1 (HOK Hsnd)) as SV1. rewrite EFm in SV1. cbn [fst] in SV1. clear Hsnd.
        pose proof (si_ml _ SV1) as Rml. pose proof (si_ms _ SV1) as Rms.
        zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
        + (* [comment removed for export] *)
          pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
          destruct SI1 as (_ & DOUT1 & ROOM1 & _).
          zstep. zs. zs. zstep. zs. zs. zs. name_mem mB.
          zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; [| exfalso; lia].
          tr_groups MUf WMf.
          unfold slowR in KLO. replace (wz 2) with (wz (ds_match_length (prev_st X1))) by reflexivity.
          eapply (KLO X1 EFm ltac:(lia)).
          split; [split|].
          * exact ZS.
          * unfold prev_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; eapply rw_cells_sim; [exact GA| cells_sim_tac; apply le4_sx32_wz; lia]
                 | exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS0 | exact LAY1].
          * split; [apply (dout_munch _ mA mB L rest0 _ DOUT1 ROOM1 MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM1|]. split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| eassumption].
        + (* [comment removed for export] *)
          unfold slowR in KHASH. eapply (KHASH X1 EFm ltac:(lia)). exact SI1. }
    zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
    + (* [comment removed for export] *)
      eapply CONT. replace (flush =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
    + zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * (* [comment removed for export] *)
        replace (flush =? 0) with true in EFm by (symmetry; apply Z.eqb_eq; lia).
        replace (ds_lookahead X1 <? 262) with true in EFm by (symmetry; apply Z.ltb_lt; lia).
        zstep. zstep. unfold SKret, Z_SLOW_EPI, slowR in KRET. eapply (KRET X1 EFm). exact SI1.
      * eapply CONT. replace (ds_lookahead X1 <? 262) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

End FILL.
