(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model Z_defl_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section PUT4.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_put4 : forall (Q : machine_state -> Prop) (X : deflate_state) (pc : Z)
    (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m : mem),
  pc = 0x17160 \/ pc = 0x17e30 ->
  DINV L rest0 lo r me X m ->
  0 <= ds_pending X -> ds_pending X + 4 <= 65536 -> 0 <= cs_adler (ds_strm X) < 2^64 ->
  (forall (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 : word) (m' : mem),
     DINV L rest0 lo r me (put_adler X) m' ->
     evt psegs Q (MS (deflR L flush r z1 z5 z6 z7 (wz (dl_S L)) z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31)
                     F (wz (pc + 112)) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz (cs_adler (ds_strm X))) y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                  F (wz pc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPC (DR & DOUT & ROOM & FR & STK & MU & WM & MI) RP0 RP4 RA HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as Lpend.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  remember (cs_adler (ds_strm X)) as a eqn:Ea.
  assert (R3 : 0 <= Z.shiftr a 24 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (R2 : 0 <= Z.shiftr a 16 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (R1 : 0 <= Z.shiftr a 8 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  destruct HPC as [-> | ->].
  - do 6 zs.
    pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b3 a RA)).
    do 6 zs.
    pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) 65536 (dl_Ab L) (ds_pending X + 1)
      (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b2 a RA)).
    do 7 zs.
    pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b1 a RA)).
    do 5 zs.
    pb_store Gpend (arr_set (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
                     (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1 + 1) (wrap8 (Z.land (Z.land a 65535) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b0 a RA)).
    name_mem mB. tr_groups MUf WMf.
    eapply HK.
    split; [split|].
    + unfold put_adler, putShortMSB, put_byte. dsred. rewrite Ea in ZS. do 4 eexists. exact ZS.
    + unfold put_adler, putShortMSB, put_byte. rewrite <- Ea.
      constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1].
    + split; [unfold put_adler, putShortMSB, put_byte; dsred; apply (dout_munch _ m mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
      split; [unfold put_adler, putShortMSB, put_byte; dsred; exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
  - do 6 zs.
    pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b3 a RA)).
    do 6 zs.
    pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) 65536 (dl_Ab L) (ds_pending X + 1)
      (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b2 a RA)).
    do 7 zs.
    pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)) ltac:(rewrite unsigned_lit by lia; exact (adler_b1 a RA)).
    do 5 zs.
    pb_store Gpend (arr_set (arr_set (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8))) (ds_pending X + 1) (wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255)))
                     (ds_pending X + 1 + 1) (wrap8 (Z.shiftr (Z.land a 65535) 8)))
      65536 (dl_Ab L) (ds_pending X + 1 + 1 + 1) (wrap8 (Z.land (Z.land a 65535) 255)) ltac:(rewrite unsigned_lit by lia; exact (adler_b0 a RA)).
    name_mem mB. tr_groups MUf WMf.
    eapply HK.
    split; [split|].
    + unfold put_adler, putShortMSB, put_byte. dsred. rewrite Ea in ZS. do 4 eexists. exact ZS.
    + unfold put_adler, putShortMSB, put_byte. rewrite <- Ea.
      constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1].
    + split; [unfold put_adler, putShortMSB, put_byte; dsred; apply (dout_munch _ m mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
      split; [unfold put_adler, putShortMSB, put_byte; dsred; exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End PUT4.
