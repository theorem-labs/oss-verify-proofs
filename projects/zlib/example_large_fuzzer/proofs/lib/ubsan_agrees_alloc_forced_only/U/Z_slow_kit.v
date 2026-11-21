(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Export Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz DeflateBlk FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition Z_SLOW_HEAD : Z := 0x1a134.      (* [comment removed for export] *)
Definition Z_SLOW_AVAIL : Z := 0x1a114.     (* [comment removed for export] *)
Definition Z_SLOW_LTAIL : Z := 0x1a714.     (* [comment removed for export] *)
Definition Z_SLOW_TAIL : Z := 0x1a750.      (* [comment removed for export] *)
Definition Z_SLOW_EPI : Z := 0x1a994.       (* [comment removed for export] *)
Definition Z_SLOW_TRAP : Z := 0x1a9d0.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition slow_post_gen (r : sregs) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (dF : deflate_state) (code : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz code) a1 a2 a3 a4 a5 a6 a7
                  (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
             F (ret_pc (r_ra r)) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
              (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
              (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned (r_sp r))
    /\ DREP m' L dF /\ din m' L inp /\ dout m' L rest0 (ds_strm dF).

(* [comment removed for export] *)
Definition slow_frame (fj : list byte) (r : sregs) : list cell :=
  [CB 8 fj; C8 (wz 4097); C8 (wz 4294967295); C8 (r_s11 r); C8 (r_s10 r); C8 (r_s9 r); C8 (r_s8 r); C8 (r_s7 r); C8 (r_s6 r);
   C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].

Definition slow_W (L : dlay) (rest0 : list byte) (lo : Z) (r : sregs) : list ivl :=
  [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
   (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
   (dl_NO L, dl_NO L + Z.of_nat (length rest0))].

(* [comment removed for export] *)
Definition slowR (L : dlay) (flush : Z) (r : sregs) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : bvmap 5 word :=
  mkR x1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) x5 x6 x7 (wz (dl_As L)) (wz flush) x10 x11 x12 x13 x14 x15 x16 x17
      (wz (18446744073709551615 - (dl_As L + 2504))) (wz (dl_As L + 5888)) (wz (dl_As L + 212)) (wz (18446744073709551615 - (dl_As L + 212)))
      (wz 18446744073709551615) (wz 261) (wz 31) (wz 3) (wz 32) (wz (dl_As L + 2504)) x28 x29 x30 x31.

(* [comment removed for export] *)
Record slow_ctx (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (me : mem) : Prop := mkSctx {
  sc_lo : lo <= bv_unsigned (r_sp r) - Z_SLOW_STACK;
  sc_sp16 : bv_unsigned (r_sp r) mod 16 = 0;
  sc_lay : dlay_ok L;
  sc_bel : dlay_below L lo (bv_unsigned (r_sp r));
  sc_io : dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo;
  sc_relro : relro_clean me;
  sc_din : din me L inp }.

(* [comment removed for export] *)
Lemma dout_munch : forall W m m' L rest0 c, dout m L rest0 c -> Box (length (cs_out_rev c) <= length rest0)%nat ->
  munch W m m' -> wmono usegs m m' -> disjoint_from W (dl_NO L) (Z.of_nat (length rest0)) -> dout m' L rest0 c.
Proof.
  intros W m m' L rest0 c D [R] MU WM DJ. unfold dout in *. eapply u8arr_transport; [exact D| exact MU| exact WM|].
  rewrite (outv_length rest0 c R). exact DJ.
Qed.

(* [comment removed for export] *)
Definition SINV (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (me : mem) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ dout m L rest0 (ds_strm X) /\ Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat
  /\ rw_cells usegs m (bv_unsigned (r_sp r) + -128) (slow_frame fj r)
  /\ stk usegs m lo (bv_unsigned (r_sp r) + -128)
  /\ munch (slow_W L rest0 lo r) me m /\ wmono usegs me m /\ mem_inv usegs m.

(* [comment removed for export] *)
Definition SK (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (pc : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me X m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom usegs)).

(* [comment removed for export] *)
Definition SKret (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (code : Z) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me X m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz code) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz Z_SLOW_EPI) fc None m' (seg_rom usegs)).

(* [comment removed for export] *)
Definition Z_SLOW_HASH : Z := 0x1a15c.
Definition KH (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  SK L flush rest0 lo r fj F fc me Q Z_SLOW_HASH X.

(* [comment removed for export] *)
Definition Z_SLOW_DECIDE : Z := 0x1a2ac.
Definition KD (L : dlay) (flush : Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem)
    (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me X m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_match_length X)) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz Z_SLOW_DECIDE) fc None m' (seg_rom usegs)).

Section KIT.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
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

(* [comment removed for export] *)
Lemma slow_epi : forall (dF : deflate_state) (code : Z), SKret L flush rest0 lo r fj F fc me (slow_post_gen r F fc L dF code inp rest0 lo me) code dF.
Proof.
  intros dF code. unfold SKret. intros until m'. intros (DR & DOUT & _ & FR & STK & MU & WM & MI). unfold slow_frame in FR. unfold Z_SLOW_EPI, slowR.
  pose proof (slow_din m' MU) as DIN. unfold slow_W in MU.
  pose proof (sc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_SLOW_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 15 zs.
  release_frame FR STK (bv_unsigned (r_sp r)).
  apply evt_done. unfold slow_post_gen. do 14 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.
End KIT.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma av8_write_le1 : forall m A a n i (w : word) v,
  u8arr usegs m A (av8 a n) -> 0 <= i < n -> n <= arr_len a -> bv_unsigned w mod 2^8 = v mod 2^8 ->
  u8arr usegs (write_to_mem m (wa (A + i)) (le1 w)) A (av8 (arr_set a i v) n).
Proof. intros m A a n i w v ARR Hi Hn E. rewrite (le1_Z8 w v E). apply (av8_write m A a n i _ v ARR Hi Hn eq_refl). Qed.

Ltac pb_store ARR a n A idx v RNG :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok usegs _ A (av8 a n) idx (wa (A + idx)) ARR ltac:(lia) eq_refl) as SOK;
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
  pose proof (u16arr_store_ok usegs _ A (avct fc dl n) (2 * idx) (wa (A + 2 * (2 * idx))) ARR ltac:(rewrite avct_length; lia) eq_refl) as SOK;
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
  pose proof (u16arr_store_ok usegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* 1.4 UBSan: the GOT slots of _length_code / _dist_code (1.3.1: 0x2c280 / 0x2c288, lemma got_tables_cells) are gone;
   1.4 made both tables file-static and deflate_slow addresses them pc-relative (auipc + add), so no walk reads the
   GOT for them (a worker's small U/Z_slow_kit, the same change as a worker's P/Z_slow_kit). *)

(* [comment removed for export] *)
Ltac ld8ro TAB a n A idx v Ev RNG :=
  let RD := fresh "RD" in
  pose proof (u8ro_read usegs _ A (av8 a n) idx (Z_to_bv 8 (arr_get a idx)) (wa (A + idx)) TAB (av8_nth a n idx ltac:(lia)) ltac:(lia) eq_refl) as RD;
  let RV := fresh "R" v in
  assert (RV : 0 <= arr_get a idx < 256) by RNG;
  remember (arr_get a idx) as v eqn:Ev;
  zs; cbv beta; rewrite (bv8_small v) by lia; clear RD.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sub_guard : forall ss bs, 0 <= ss < 2 ^ 62 -> - 2 ^ 62 <= bs <= ss ->
  Z.b2z (9223372036854775808 <? Z.lxor (bs mod 18446744073709551616) 9223372036854775808)
  = Z.b2z (Z.lxor ((ss - bs mod 18446744073709551616) mod 18446744073709551616) 9223372036854775808 <? Z.lxor ss 9223372036854775808).
Proof.
  intros ss bs Hss Hbs. change (Z.lxor ?a 9223372036854775808) with (Z.lxor a (2^63)).
  rewrite !zb_lxor_sign by (Z.div_mod_to_equations; lia).
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  match goal with |- Z.b2z (?a <? ?b) = Z.b2z (?c <? ?d) =>
    destruct (Z.ltb_spec a b); destruct (Z.ltb_spec c d); try reflexivity; exfalso; Z.div_mod_to_equations; lia end.
Qed.

Lemma sub_guard_pos : forall ss bs, 0 <= ss < 2 ^ 62 -> 0 <= bs <= ss ->
  Z.b2z (9223372036854775808 <? Z.lxor bs 9223372036854775808)
  = Z.b2z (Z.lxor (ss - bs) 9223372036854775808 <? Z.lxor ss 9223372036854775808).
Proof.
  intros ss bs Hss Hbs. change (Z.lxor ?a 9223372036854775808) with (Z.lxor a (2^63)).
  rewrite !zb_lxor_sign by (Z.div_mod_to_equations; lia).
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  match goal with |- Z.b2z (?a <? ?b) = Z.b2z (?c <? ?d) =>
    destruct (Z.ltb_spec a b); destruct (Z.ltb_spec c d); try reflexivity; exfalso; Z.div_mod_to_equations; lia end.
Qed.
