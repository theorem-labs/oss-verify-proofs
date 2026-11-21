(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit Z_flushpend Z_ukit Z_slow_fbA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel DeflateSafe DeflateOverlay
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6 RefDeflSafeLF RefDeflSafeFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section SITE.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HTFBLK : tr_flush_block_stmtE.   (* [comment removed for export] *)
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Lemma slow_fbC : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  flush_ok X 1 -> fb_entry X 1 -> ds_lit_bufsize X = 16384 -> ds_w_size X = 32768 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_block_only X 1))) <= length rest0)%nat ->
  SK L flush rest0 lo r fj F fc me Q 0x1a910 (flush_block_only X 1) ->
  evt usegs Q (MS (slowR L flush r x1 x5 x6 x7 (wz (ds_strstart X)) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a858) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & _ & FR & STK & MU & WM & MI) FOK FE LBS WSX RAO ROOM HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  assert (OL0 : (length (cs_out_rev (ds_strm X)) <= length rest0)%nat) by (pose proof (fbo_out_mono X 1); lia).
  pose proof (outv_length rest0 (ds_strm X) OL0) as OL. clear OL0.
  apply box in ROOM.
  destruct (fbo_buf_ok X 1 FOK WSX) as (BOK & ELEN & EBP & EBN).
  destruct (flush_ok_fbo X 1 FOK LBS) as (FBS & BI & Rdiff & Rbs & Rss & Rla & Rwb & _).
  destruct (fbo2_facts X 1 FOK LBS RAO) as (FP2 & LB2 & RAO2 & ES2 & E1 & EO).
  rewrite WSX in Rss, Rla.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (RBS : - 2^63 <= ds_block_start X < 2^63) by lia.
  (* [comment removed for export] *)
  zs. zstep.
  eapply (evt_cut usegs (fun ms' => exists v10 v13 v14, ms' = MS (slowR L flush r x1 x5 x6 x7 v10 (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end)) (wz (fb_len X))
                                                                   v13 v14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a8f4) fc None m (seg_rom usegs))).
  { if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      assert (NEG : ds_block_start X < 0) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zstep. zstep. zstep. zstep.
      rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia. gF.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBN NEG).
      replace (wz (ds_strstart X - ds_block_start X mod 18446744073709551616)) with (wz (fb_len X))
        by (apply Z_to_bv_eqm; rewrite ELEN; Z.div_mod_to_equations; lia).
      reflexivity.
    - assert (POS : 0 <= ds_block_start X) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zs. zs. zstep. rewrite ?Z.mod_small by lia.
      replace (Z.land (ds_block_start X) 4294967295) with (ds_block_start X)
        by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      zstep. gF. zstep. zstep. zstep. gX.
      zstep. zstep. zstep.
      first [rewrite (sub_guard_pos (ds_strstart X) (ds_block_start X)) by lia | rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia]. gT.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBP POS).
      replace (wz (ds_strstart X - ds_block_start X)) with (wz (fb_len X)) by (f_equal; rewrite ELEN; reflexivity).
      reflexivity. }
  intros ms' (v10 & v13 & v14 & ->). unfold slowR.
  assert (RL : relro_clean m) by (apply (slow_relro L inp rest0 lo r me CTX); exact MU).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold dout in DOUT.
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  call (HTFBLK L X (fb_buf X) (fb_len X) 1 lo).
  1:{ exact DR0. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. } 1:{ unfold Z_TRFB_STACK in *. rewrite ESP. lia. }
  1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. }
  1:{ exact BI. } 1:{ exact FBS. } 1:{ exact FE. } 1:{ exact BOK. } 1:{ unfold fb_len. apply wrap64_range. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA. rewrite ESP in PC.
  change (tr_flush_block X (fb_buf X) (fb_len X) 1) with (fbo1 X 1) in POST.
  remember (fbo1 X 1) as X1 eqn:EX1.
  assert (DOUT1 : u8arr usegs mA (dl_NO L) (outv rest0 (ds_strm X1))) by (unfold outv; rewrite EO; exact DOUT).
  assert (OL1 : length (outv rest0 (ds_strm X1)) = length rest0) by (unfold outv; rewrite EO; exact OL).
  clear DOUT OL.
  destruct POST as [ZS ST]. open_zs ZS.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS1 LAY1]. open_A GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  (* [comment removed for export] *)
  zs. rewrite ?Z.mod_small by lia. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  remember (set_block_start X1 (ds_strstart X1)) as X2 eqn:EX2.
  assert (EF2 : fbo2 X 1 = X2) by (rewrite EX2, EX1; reflexivity). rewrite EF2 in FP2, LB2, RAO2, ES2.
  assert (DR2 : DREP mB L X2).
  { split.
    - rewrite ES2. do 4 eexists. exact ZS.
    - rewrite EX2. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS1 | exact LAY1]. }
  assert (DOUT2 : dout mB L rest0 (ds_strm X2)) by (unfold dout; rewrite ES2; exact DOUT1).
  assert (RM2 : (length (cs_out_rev (ds_strm (flush_pending X2))) <= length rest0)%nat) by (rewrite <- EF2, <- fbo_fp; exact (unbox _ ROOM)).
  clear MUf WMf GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend ZS DOUT1.
  (* [comment removed for export] *)
  zstep.
  call (flush_pending_spec HTFB L X2 rest0 (zlength inp) lo).
  1:{ exact DR2. } 1:{ exact DOUT2. } 1:{ exact MI0. } 1:{ rewrite ESP. exact PC. } 1:{ rewrite ESP. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. }
  1:{ exact FP2. } 1:{ exact LB2. } 1:{ exact RAO2. } 1:{ exact RM2. } 1:{ reflexivity. }
  name_mem mC.
  lazymatch goal with H : stk usegs mC lo _ |- _ => rewrite ?ESP in H; rename H into STKF end.
  lazymatch goal with H : DREP mC L _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DRF end.
  lazymatch goal with H : dout mC L rest0 _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DOUTF end.
  lazymatch goal with H : mem_inv usegs mC |- _ => rename H into MIF end.
  eapply HK.
  split; [exact DRF|]. split; [exact DOUTF|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STKF|]. split; [exact MU|]. split; [exact WM| exact MIF].
Qed.
End SITE.
