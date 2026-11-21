(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_SLOW_HEAD : Z := 0x19904.
Definition Z_SLOW_LTAIL : Z := 0x198e0.
Definition Z_SLOW_TAIL : Z := 0x19e18.
Definition Z_SLOW_EPI : Z := 0x1a068.

Record sregs : Type := mkSR {
  r_ra : word; r_sp : word; r_gp : word; r_tp : word;
  r_s0 : word; r_s1 : word; r_s2 : word; r_s3 : word; r_s4 : word; r_s5 : word;
  r_s6 : word; r_s7 : word; r_s8 : word; r_s9 : word; r_s10 : word; r_s11 : word }.

Definition slow_post_gen (r : sregs) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (dF : deflate_state) (code : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz code) a1 a2 a3 a4 a5 a6 a7
                  (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
             F (ret_pc (r_ra r)) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
              (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
              (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned (r_sp r))
    /\ DREP m' L dF /\ din m' L inp /\ dout m' L rest0 (ds_strm dF).

(* 1.4 (zl14-cmp): deflate_slow keeps flush in s1 (mv s1,a1), not in a frame slot; 4097 moves to sp+8 and
   0xffffffff to sp+16; sp+0 is never written (j0: the carve's 8 junk bytes, existential in SINV). *)
Definition slow_frame (j0 : list byte) (r : sregs) : list cell :=
  [CB 8 j0; C8 (wz 4097); C8 (wz 4294967295); C8 (r_s11 r); C8 (r_s10 r); C8 (r_s9 r); C8 (r_s8 r); C8 (r_s7 r); C8 (r_s6 r);
   C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].

Definition slow_W (L : dlay) (rest0 : list byte) (lo : Z) (r : sregs) : list ivl :=
  [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
   (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
   (dl_NO L, dl_NO L + Z.of_nat (length rest0))].

Definition slowR (L : dlay) (r : sregs) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x28 x29 x30 x31 : word) : bvmap 5 word :=
  mkR x1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) x5 x6 x7 (wz (dl_As L)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (wz 65535) (wz (dl_As L + 5888)) (wz (dl_As L + 212)) (wz (-1)) (wz 262) x25 (wz 3) (wz (dl_As L + 2504)) x28 x29 x30 x31.

Record slow_ctx (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) : Prop := mkSctx {
  sc_lo : lo <= bv_unsigned (r_sp r) - Z_SLOW_STACK;
  sc_sp16 : bv_unsigned (r_sp r) mod 16 = 0;
  sc_lay : dlay_ok L;
  sc_bel : dlay_below L lo (bv_unsigned (r_sp r));
  sc_io : dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo;
  sc_relro : relro_clean me;
  sc_din : din me L inp }.

Inductive Box (P : Prop) : Prop := box : P -> Box P.
Lemma unbox : forall P : Prop, Box P -> P.
Proof. intros P [H]. exact H. Qed.

Lemma dout_munch : forall W m m' L rest0 c, dout m L rest0 c -> Box (length (cs_out_rev c) <= length rest0)%nat ->
  munch W m m' -> wmono psegs m m' -> disjoint_from W (dl_NO L) (Z.of_nat (length rest0)) -> dout m' L rest0 c.
Proof.
  intros W m m' L rest0 c D [R] MU WM DJ. unfold dout in *. eapply u8arr_transport; [exact D| exact MU| exact WM|].
  rewrite (outv_length rest0 c R). exact DJ.
Qed.

Definition SINV (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ dout m L rest0 (ds_strm X) /\ Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat
  /\ (exists j0, rw_cells psegs m (bv_unsigned (r_sp r) + -128) (slow_frame j0 r))
  /\ stk psegs m lo (bv_unsigned (r_sp r) + -128)
  /\ munch (slow_W L rest0 lo r) me m /\ wmono psegs me m /\ mem_inv psegs m.

Definition SK (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom psegs)).

Definition SKx (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                          y20 (wz (dl_As L + 5888)) (wz (dl_As L + 212)) (wz (-1)) (wz 262) y25 (wz 3) (wz (dl_As L + 2504)) y28 y29 y30 y31)
                     F (wz pc) fc None m' (seg_rom psegs)).

Definition SKret (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (code : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz code) y11 y12 y13 y14 y15 y16 y17 y18 y19
                          y20 (wz (dl_As L + 5888)) (wz (dl_As L + 212)) (wz (-1)) (wz 262) y25 (wz 3) (wz (dl_As L + 2504)) y28 y29 y30 y31)
                     F (wz Z_SLOW_EPI) fc None m' (seg_rom psegs)).

Definition Z_SLOW_HASH : Z := 0x19950.
Definition KH (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 w13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me X m' -> le4 w13 = le4 (wz (ds_match_start X)) ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 (wz (ds_match_length X)) w13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz Z_SLOW_HASH) fc None m' (seg_rom psegs)).

Definition Z_SLOW_DECIDE : Z := 0x19a34.
Definition KD (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_match_length X)) y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz Z_SLOW_DECIDE) fc None m' (seg_rom psegs)).

Section KIT.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma slow_relro : forall m, munch (slow_W L rest0 lo r) me m -> relro_clean m.
Proof.
  intros m MU. destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp.
  eapply relro_clean_munch; [exact RELRO| exact MU|]. unfold slow_W, RELRO_LO, RELRO_HI. cbn [disjoint_from].
  below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_s L LAY) as (_ & _ & _ & Is). pose proof (lo_w L LAY) as (_ & _ & _ & Iw). pose proof (lo_p L LAY) as (_ & _ & _ & Ip).
  pose proof (lo_h L LAY) as (_ & _ & _ & Ih). pose proof (lo_b L LAY) as (_ & _ & _ & Ib). pose proof (io_img _ _ _ _ IO) as Io.
  repeat split; lia.
Qed.

Lemma slow_din : forall m, munch (slow_W L rest0 lo r) me m -> din m L inp.
Proof.
  intros m MU. destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. unfold din in *.
  eapply bytes_at_transport; [exact DIN| exact MU|]. unfold slow_W. cbn [disjoint_from]. rewrite zb8_length.
  below_open BEL. pose proof IO as I0. io_open I0. unfold zlength in *.
  pose proof (io_is _ _ _ _ IO) as J1. pose proof (io_iw _ _ _ _ IO) as J2. pose proof (io_ip _ _ _ _ IO) as J3.
  pose proof (io_ih _ _ _ _ IO) as J4. pose proof (io_ib _ _ _ _ IO) as J5. pose proof (io_io _ _ _ _ IO) as J6.
  unfold apart, zlength in *. repeat split; lia.
Qed.

Lemma slow_epi : forall (dF : deflate_state) (code : Z), SKret L flush rest0 lo r F fc me (slow_post_gen r F fc L dF code inp rest0 lo me) code dF.
Proof.
  intros dF code. unfold SKret. intros until m'. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI). unfold slow_frame in FR. unfold Z_SLOW_EPI.
  pose proof (slow_din m' MU) as DIN. unfold slow_W in MU.
  pose proof (sc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_SLOW_STACK in LOsp.
  do 15 zs.
  release_frame FR STK (bv_unsigned (r_sp r)).
  apply evt_done. unfold slow_post_gen. do 14 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.
End KIT.

Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].

Ltac with_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
Ltac name_mem id := with_mem ltac:(fun mm => rename mm into id).

Lemma le4_sx32_wz : forall v, 0 <= v < 2^32 -> le4 (sx32 (wz v)) = le4 (wz v).
Proof.
  intros v Hv. apply le4_wz_mod. unfold sx32. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div].
  change (2 ^ 32) with 4294967296 in *. change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma toofar_mach : forall ss ms, 0 <= ms < 2^32 ->
  (bv_swrap 32 (ss - bv_unsigned (sx32 (wz ms))) mod 18446744073709551616 < 4097 <-> wrap32 (ss - ms) <= 4096).
Proof.
  intros ss ms Hms. unfold sx32. rewrite !Z_to_bv_unsigned, wrap32_mod.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma Z8_eqm : forall x y, x mod 2^8 = y mod 2^8 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.

Lemma le1_Z8 : forall (w : word) v, bv_unsigned w mod 2^8 = v mod 2^8 -> le1 w = [Z_to_bv 8 v].
Proof. intros w v H. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z8_eqm. exact H. Qed.

Lemma av8_write_le1 : forall m A a n i (w : word) v,
  u8arr psegs m A (av8 a n) -> 0 <= i < n -> n <= arr_len a -> bv_unsigned w mod 2^8 = v mod 2^8 ->
  u8arr psegs (write_to_mem m (wa (A + i)) (le1 w)) A (av8 (arr_set a i v) n).
Proof. intros m A a n i w v ARR Hi Hn E. rewrite (le1_Z8 w v E). apply (av8_write m A a n i _ v ARR Hi Hn eq_refl). Qed.

Ltac pb_store ARR a n A idx v RNG :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok psegs _ A (av8 a n) idx (wa (A + idx)) ARR ltac:(lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av8_write_le1 m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(RNG)) as ARR';
      replace (A + idx) with E in ARR' by lia;
      let LN := fresh "LPB" in pose proof (av8_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNP" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Ltac ct_store_fc ARR fc dl n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (avct fc dl n) (2 * idx) (wa (A + 2 * (2 * idx))) ARR ltac:(rewrite avct_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (avct_write_fc m0 A fc dl n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * (2 * idx)) with E in ARR' by lia;
      let LN := fresh "LCT" in pose proof (avct_zlength (arr_set fc idx v) dl n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set fc idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Ltac st16 ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Ltac close_lens_set LENS :=
  let l1 := fresh in let l2 := fresh in let l3 := fresh in let l4 := fresh in let l5 := fresh in let l6 := fresh in let l7 := fresh in
  let l8 := fresh in let l9 := fresh in let l10 := fresh in let l11 := fresh in let l12 := fresh in let l13 := fresh in
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
  constructor; FillWinModel.dsred; rewrite ?arr_len_set;
  [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact l10| exact l11| exact l12| exact l13].

(* 1.4 (zl14-cmp): the GOT slots of _length_code / _dist_code (1.3.1: 0x29380 / 0x29388, lemma got_tables_cells)
   are gone; 1.4 made both tables file-static and addresses them pc-relative, so the walks read no GOT. *)

Ltac ld8ro TAB a n A idx v Ev RNG :=
  let RD := fresh "RD" in
  pose proof (u8ro_read psegs _ A (av8 a n) idx (Z_to_bv 8 (arr_get a idx)) (wa (A + idx)) TAB (av8_nth a n idx ltac:(lia)) ltac:(lia) eq_refl) as RD;
  let RV := fresh "R" v in
  assert (RV : 0 <= arr_get a idx < 256) by RNG;
  remember (arr_get a idx) as v eqn:Ev;
  zs; cbv beta; rewrite (bv8_small v) by lia; clear RD.

Definition dist_reg (ss pm : Z) : Z :=
  bv_swrap 32 (bv_unsigned (wz ss) + Z.lxor (bv_unsigned (sx32 (wz pm))) 18446744073709551615).

Lemma dist_reg_facts : forall ss pm, 0 <= ss <= 65536 -> 0 <= pm < 2^32 ->
  - 2^31 <= dist_reg ss pm < 2^31 /\ dist_reg ss pm mod 2^32 = (ss - 1 - pm) mod 2^32.
Proof.
  intros ss pm Hss Hpm. unfold dist_reg.
  assert (Rx : 0 <= bv_unsigned (sx32 (wz pm)) < 2^64) by (pose proof (bv_unsigned_in_range 64 (sx32 (wz pm))) as R; unfold bv_modulus in R; cbn in R; lia).
  rewrite (zb_lxor_ones _ Rx). rewrite unsigned_lit by lia.
  assert (E : bv_unsigned (sx32 (wz pm)) mod 2^32 = pm mod 2^32).
  { unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *.
    Z.div_mod_to_equations. lia. }
  remember (bv_unsigned (sx32 (wz pm))) as u eqn:Eu. clear Eu.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648. change (2^64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma tally_b0 : forall dv e, dv mod 2^32 = e mod 2^32 -> bv_unsigned (wz dv) mod 2^8 = wrap8 (wrap16 (wrap32 e)) mod 2^8.
Proof.
  intros dv e E. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. unfold wrap8, wrap16, wrap32.
  change 255 with (Z.ones 8). change 65535 with (Z.ones 16). change 4294967295 with (Z.ones 32). rewrite !Z.land_ones by lia.
  change (2^64) with 18446744073709551616. change (2 ^ 32) with 4294967296 in *. change (2^16) with 65536. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

Lemma tally_b1 : forall dv e, dv mod 2^32 = e mod 2^32 ->
  bv_unsigned (wz (Z.shiftr (Z.land dv 18446744073709551615) 8)) mod 2^8 = wrap8 (Z.shiftr (wrap16 (wrap32 e)) 8) mod 2^8.
Proof.
  intros dv e E. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. unfold wrap8, wrap16, wrap32.
  change 255 with (Z.ones 8). change 65535 with (Z.ones 16). change 4294967295 with (Z.ones 32). rewrite !Z.land_ones by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616. change (2 ^ 32) with 4294967296 in *. change (2^16) with 65536. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

Lemma tally_dd : forall dv e, dv mod 2^32 = e mod 2^32 ->
  Z.land (Z.land (dv + -1) 18446744073709551615) 65535 = (e + -1) mod 2^16.
Proof.
  intros dv e E. change 18446744073709551615 with (Z.ones 64). change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
  change (2 ^ 32) with 4294967296 in *. change (2^16) with 65536. change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma le2_sx16_inc : forall v, 0 <= v < 65536 -> le2 (wz (bv_unsigned (sx16 (wz v)) + 1)) = le2 (wz (wrap16 (v + 1))).
Proof.
  intros v Hv. apply le2_wz_mod. unfold sx16. rewrite !Z_to_bv_unsigned. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (65536 / 2) with 32768. change (2^16) with 65536. Z.div_mod_to_equations. lia.
Qed.

Lemma le2_swrap16_inc : forall v, 0 <= v < 65536 ->
  le2 (wz (bv_swrap 16 (Z.land v 18446744073709551615) + 1)) = le2 (wz (wrap16 (v + 1))).
Proof.
  intros v Hv. apply le2_wz_mod. rewrite Z_to_bv_unsigned. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (65536 / 2) with 32768. change (2^16) with 65536. change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma le2_sx16_wz : forall v, 0 <= v < 65536 -> le2 (sx16 (wz v)) = le2 (wz v).
Proof.
  intros v Hv. apply le2_wz_mod. unfold sx16. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (65536 / 2) with 32768. change (2^16) with 65536. Z.div_mod_to_equations. lia.
Qed.

Lemma tally_b1_mod : forall dv e, dv mod 2^32 = e mod 2^32 ->
  bv_unsigned (wz (Z.shiftr (dv mod 18446744073709551616) 8)) mod 2^8 = wrap8 (Z.shiftr (wrap16 (wrap32 e)) 8) mod 2^8.
Proof.
  intros dv e E. rewrite <- (tally_b1 dv e E). change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma tally_dd_mod : forall dv e, dv mod 2^32 = e mod 2^32 ->
  Z.land ((dv + -1) mod 18446744073709551616) 65535 = (e + -1) mod 2^16.
Proof.
  intros dv e E. rewrite <- (tally_dd dv e E). change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma le2_swrap16_inc_mod : forall v, 0 <= v < 65536 ->
  le2 (wz (bv_swrap 16 (v mod 18446744073709551616) + 1)) = le2 (wz (wrap16 (v + 1))).
Proof.
  intros v Hv. rewrite <- (le2_swrap16_inc v Hv). change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity.
Qed.
