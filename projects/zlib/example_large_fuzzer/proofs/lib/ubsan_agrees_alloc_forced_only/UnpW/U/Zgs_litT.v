(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Section LITT.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Ltac sym_step := zs; zs.
Ltac sym_guards := zstep; zstep; zs; gF; zstep; zstep; zstep; gX; gF.
Lemma slow_tlitT : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_inv X -> 1 <= ds_strstart X -> ds_strstart X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  SK L flush rest0 lo r fj F fc me Q 0x1a838 (break1_st X) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a758) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) SV SS1 SS2 WS LBS HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_b _ LAY) as BKb. unfold blk_ok in BKb. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU. unfold SK, slowR in HK.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. zs. zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
  sym_step.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + -1) ltac:(apply Rwb; lia).
  pose proof (Rwb (ds_strstart X + -1) ltac:(lia)) as Rc.
  sym_guards.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0) ltac:(reflexivity).
  sym_step. sym_guards.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0) ltac:(reflexivity).
  sym_step. sym_guards.
  remember (arr_get (ds_window X) (ds_strstart X + -1)) as c eqn:Ec.
  assert (Ewc : wrap8 c = c) by (apply wrap8_id; lia).
  zstep.
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 c)) ltac:(rewrite unsigned_lit by lia; rewrite !Ewc; reflexivity).
  rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  gF. zstep.
  replace (wz (dl_As L + 212 + c * 4)) with (wz (dl_As L + 212 + 4 * c)) by (f_equal; lia).
  pose proof (u16arr_read usegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * wrap8 c)
                (wz (arr_get (ds_dyn_ltree_fc X) (wrap8 c))) (wa (dl_As L + 212 + 4 * c)) Glt
                (avct_nth_fc _ _ 573 (wrap8 c) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zstep.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc X) (wrap8 c) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).
  zs. name_mem mB.
  tr_groups MUf WMf.
  eapply HK.
  subst c. unfold break1_st, slit1. cbv zeta. replace (ds_strstart X - 1) with (ds_strstart X + -1) by lia.
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End LITT.
