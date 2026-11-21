(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_defl_iface Z_fw_model Z_fw_kit Z_fw_high Z_readbuf Z_ukit Zg_adler32_iface Zg_readbuf Zg_fw_model Zg_fw_insert Zg_fw_tail.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section READ.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.
Hypothesis HADL : adler32_stmt.

Lemma fwg_read : forall (X : deflate_state) (more : Z)
    (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y19 y23 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r me X m -> fw_wf 32768 32768 X -> ds_wrap X <> 2 -> cs_avail_in (ds_strm X) < 2^31 ->
  din_tie inp X ->
  more = ds_window_size X - ds_lookahead X - ds_strstart X -> (more = 0 -> 262 < ds_lookahead X) ->
  (cs_avail_in (ds_strm X) <> 0 -> 262 <= ds_lookahead X + more) ->
  evt usegs (fw_post_gen r F fc L (fill_window_high (fwB X more)) inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz more) y10 (wz (ds_strstart X)) y12 y13 y14 y15 y16 y17
             (wz (dl_As L + 5932)) y19 (wz 3) (wz 32) (wz 2) (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_FW_READ) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros INV FW W2 AI TIE EM ZM FULL. unfold Z_FW_READ.
  pose proof INV as INV0. destruct INV as (DR & DIN & (j0 & FR) & STK & MU & WM & MI). unfold fw_W in MU. unfold fw_frame in FR.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof DR as DR0. destruct DR0 as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  pose proof (lo_S _ LAY) as BKS.
  pose proof FW as FW0. destruct FW as [_ _ Wwl Wwsz _ _ _ _ _ _ _ Wins Wlook Wsl _ _ _ Wni Wai Winl Wti Wwr Wad1 _ _ _ _ _].
  pose proof TIE as [TIE1 TIE2]. rewrite TIE1, arr_len_of_list in Winl.
  open_DST ST. open_A GA. open_zs ZS.
  zs. gF. zstep. al8 (dl_S L). gF.
  zs.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  { (* [comment removed for export] *)
    rewrite (fwB_0 X more) by lia. apply (fw_high L inp nout lo r F fc me CTX X); [exact INV0| exact FW0]. }
  (* [comment removed for export] *)
  zs. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX.
  zs. zstep. gF. zstep. zstep. gX.
  (* [comment removed for export] *)
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -96)) = bv_unsigned (r_sp r) + -96) by (apply unsigned_lit; lia).
  replace (wz (ds_lookahead X + (dl_Aw L + ds_strstart X))) with (wz (dl_Aw L + (ds_strstart X + ds_lookahead X))) by (f_equal; lia).
  zstep. call (read_buf_win_spec HADL L X inp nout lo more (ds_strstart X + ds_lookahead X) (dl_Aw L + (ds_strstart X + ds_lookahead X))).
  1:{ exact DR. } 1:{ exact DIN. } 1:{ exact TIE. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_READBUF_STACK. lia. }
  1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. } 1:{ unfold dlay_below in *. rewrite ESP. lia. } 1:{ exact IO. }
  1:{ exact Wwl. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Wwr. } 1:{ exact W2. } 1:{ exact Wad1. } 1:{ exact Wni. } 1:{ lia. } 1:{ exact Winl. } 1:{ exact Wti. }
  1:{ reflexivity. }
  lazymatch goal with H : stk usegs _ lo (bv_unsigned _) |- _ => rewrite ESP in H; rename H into STK1 end.
  lazymatch goal with H : DREP _ L (fst _) |- _ => rename H into DR1 end.
  lazymatch goal with H : din _ L inp |- _ => rename H into DIN1 end.
  (* [comment removed for export] *)
  destruct (read_buf_small X (ds_strstart X + ds_lookahead X) more) as (R1 & R2 & R3 & R4 & R5 & _ & _).
  pose proof (read_buf_wf 32768 32768 X (ds_strstart X + ds_lookahead X) more FW0 eq_refl ltac:(lia) ltac:(lia)) as RW. cbv zeta in RW.
  pose proof (rb_len_range X more ltac:(lia) ltac:(lia)) as (RN1 & RN2 & RN3).
  remember (read_buf X (RB_window (ds_strstart X + ds_lookahead X)) more) as rb eqn:Erb.
  rewrite (fwB_pos X more ltac:(lia)). rewrite <- Erb.
  apply (fwg_tail L inp nout lo r F fc me CTX (fst rb) (snd rb)).
  - split; [exact DR1|]. split; [exact DIN1|]. split; [eexists; exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| assumption].
  - exact (proj1 RW).
  - rewrite R1. lia.
  - rewrite R4, R3, R1. lia.
  - rewrite R3, R2, R1. intros Hsmall. pose proof (FULL ltac:(lia)) as F2. unfold rb_len in *.
    destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); lia.
Qed.
End READ.
