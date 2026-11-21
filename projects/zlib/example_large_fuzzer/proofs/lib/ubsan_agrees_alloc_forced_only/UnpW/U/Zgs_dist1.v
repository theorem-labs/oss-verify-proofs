(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_tr_rod Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Lemma dist_reg64_facts : forall ss pm, 0 <= ss <= 65536 -> 0 <= pm < 2^32 ->
  0 <= ss + Z.lxor (bv_unsigned (sx32 (wz pm))) 18446744073709551615 < 2^65
  /\ (ss + Z.lxor (bv_unsigned (sx32 (wz pm))) 18446744073709551615) mod 2^32 = (ss - 1 - pm) mod 2^32.
Proof.
  intros ss pm Hss Hpm.
  assert (Rx : 0 <= bv_unsigned (sx32 (wz pm)) < 2^64) by (pose proof (bv_unsigned_in_range 64 (sx32 (wz pm))) as R; unfold bv_modulus in R; cbn in R; lia).
  rewrite (zb_lxor_ones _ Rx).
  assert (E : bv_unsigned (sx32 (wz pm)) mod 2^32 = pm mod 2^32).
  { unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *.
    Z.div_mod_to_equations. lia. }
  remember (bv_unsigned (sx32 (wz pm))) as u eqn:Eu. clear Eu.
  change (2 ^ 32) with 4294967296 in *. change (2^65) with 36893488147419103232. change (2^64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.
Lemma tally_b1w : forall dv e, 0 <= dv -> dv mod 2^32 = e mod 2^32 ->
  bv_unsigned (wz (bv_swrap 32 (Z.shiftr (bv_wrap 32 (dv mod 18446744073709551616)) 8))) mod 2^8 = wrap8 (Z.shiftr (wrap16 (wrap32 e)) 8) mod 2^8.
Proof.
  intros dv e Hdv E.
  assert (EW : bv_wrap 32 (dv mod 18446744073709551616) = e mod 2^32).
  { unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change (2^32) with 4294967296 in *. rewrite <- E.
    Z.div_mod_to_equations. nia. }
  rewrite EW. pose proof (Z.mod_pos_bound e (2^32) ltac:(lia)) as R.
  assert (RS : 0 <= Z.shiftr (e mod 2^32) 8 < 2^24) by (rewrite Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296 in *; change (2^8) with 256; change (2^24) with 16777216; Z.div_mod_to_equations; lia).
  rewrite bv_swrap32_id by lia. rewrite unsigned_lit by lia.
  unfold wrap8, wrap16, wrap32. change 255 with (Z.ones 8). change 65535 with (Z.ones 16). change 4294967295 with (Z.ones 32). rewrite !Z.land_ones by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 32) with 4294967296 in *. change (2^16) with 65536. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
Lemma tally_dd64 : forall dv e, 0 <= dv -> dv mod 2^32 = e mod 2^32 ->
  ((dv + -1) mod 18446744073709551616) mod 65536 = (e + -1) mod 2^16.
Proof.
  intros dv e Hdv E. change (2 ^ 32) with 4294967296 in *. change (2^16) with 65536.
  Z.div_mod_to_equations. nia.
Qed.
Lemma shl48_eqm : forall x d, 0 <= x -> x mod 65536 = d -> wz (Z.shiftl x 48) = wz (d * 281474976710656).
Proof.
  intros x d Hx E. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. change (2^48) with 281474976710656. change (2^64) with 18446744073709551616.
  rewrite <- E. Z.div_mod_to_equations. nia.
Qed.
Section DIST1.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Definition KT1 (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me (sdist1 X) m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart X)) (wz (ds_lookahead X)) (wz 70560) (wz (sdist_D X)) (wz (sdist_D X * 281474976710656)) y15 y16 y17 y28 y29 y30 y31)
                    F (wz 0x1a3ac) fc None m' (seg_rom usegs)).
Lemma slow_tdist1 : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y11 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_inv X -> 3 <= ds_prev_length X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  KT1 Q X ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_match_length X)) y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a2b8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) SV PL3 RLA WS LBS HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_b _ LAY) as BKb. unfold blk_ok in BKb. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. zs. zs. zs. zs. rewrite ?(sx32_wz (ds_strstart X)) by lia. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  zstep. zstep.
  destruct (dist_reg64_facts (ds_strstart X) (ds_prev_match X) ltac:(lia) Rpm) as [Rdv Edv].
  remember (ds_strstart X + Z.lxor (bv_unsigned (sx32 (wz (ds_prev_match X)))) 18446744073709551615) as dv eqn:Edvdef.
  clear Edvdef. apply box in Edv.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X)) ltac:(unfold sdist; apply tally_b0; exact (unbox _ Edv)).
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  zstep.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X))) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1)
    (wrap8 (Z.shiftr (sdist X) 8)) ltac:(unfold sdist; apply tally_b1w; [lia| exact (unbox _ Edv)]).
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  name_mem mB.
  zstep. zstep. zstep. zstep.
  replace (Z.land (ds_prev_length X + -3) 255) with (wrap8 (ds_prev_length X - 3)) by (unfold wrap8; f_equal; lia).
  assert (Rlc : 0 <= wrap8 (ds_prev_length X - 3) < 256) by (apply wrap8_range).
  zstep. try rewrite (zb_lxor_ones 72976) by lia.
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X))) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 (Z.shiftr (sdist X) 8)))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 (ds_prev_length X - 3)))
    ltac:(rewrite unsigned_lit by lia; unfold wrap8; change 255 with (Z.ones 8); rewrite !Z.land_ones by lia; change (2^8) with 256; Z.div_mod_to_equations; lia).
  gF. zstep.
  assert (MIB : mem_inv usegs _) by eassumption.
  pose proof (rod_length_code _ MIB) as TLC. unfold Z_LENGTH_CODE in TLC.
  ld8ro TLC length_code_a 256 72976 (wrap8 (ds_prev_length X - 3)) lcode Elcode ltac:(pose proof (length_code_range (wrap8 (ds_prev_length X - 3)) Rlc); lia).
  clear TLC.
  pose proof (length_code_range (wrap8 (ds_prev_length X - 3)) Rlc) as Rcode. rewrite <- Elcode in Rcode.
  zstep. zstep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. gF. zstep.
  pose proof (u16arr_read usegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * (lcode + 257))
                (wz (arr_get (ds_dyn_ltree_fc X) (lcode + 257))) (wa (dl_As L + 212 + (lcode + 257) * 4)) Glt
                (avct_nth_fc _ _ 573 (lcode + 257) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD. zstep. zstep.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (lcode + 257) (wrap16 (arr_get (ds_dyn_ltree_fc X) (lcode + 257) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).
  zstep. zstep. zstep.
  rewrite (tally_dd64 dv (ds_strstart X - 1 - ds_prev_match X) ltac:(lia) (unbox _ Edv)).
  replace ((ds_strstart X - 1 - ds_prev_match X + -1) mod 2 ^ 16) with (sdist_D X) by (unfold sdist_D; f_equal; lia).
  rewrite (shl48_eqm ((dv + -1) mod 18446744073709551616) (sdist_D X) ltac:(Z.div_mod_to_equations; lia)
             ltac:(rewrite (tally_dd64 dv (ds_strstart X - 1 - ds_prev_match X) ltac:(lia) (unbox _ Edv)); unfold sdist_D; f_equal; lia)).
  name_mem mC.
  tr_groups MUf WMf.
  subst lcode. unfold KT1, slowR in HK.
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold sdist1. cbv zeta. constructor;
      [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mC L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End DIST1.
