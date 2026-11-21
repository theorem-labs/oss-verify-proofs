(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model Z_fw_model Z_fw_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition Z_SH1 : Z := 0x16b2c.
Definition Z_SH1X : Z := 0x16b58.
Definition Z_SH2 : Z := 0x16b84.
Definition Z_SH2X : Z := 0x16bb0.
Definition Z_FW_TRAP : Z := 0x16e48.
Definition Z_FW_TRAPA : Z := 0x16e44.
Lemma av8_blit_down : forall a N sofs n, 0 <= n -> n <= sofs -> sofs + n <= N -> N <= arr_len a ->
  av8 (arr_blit a 0 a sofs n) N = firstn (Z.to_nat n) (skipn (Z.to_nat sofs) (av8 a N)) ++ skipn (Z.to_nat n) (av8 a N).
Proof.
  intros a N sofs n Hn Hs HN HL. apply list_ext_nth.
  - rewrite length_app, length_firstn, !length_skipn, !av8_length. lia.
  - intros j Hj. rewrite av8_length in Hj.
    replace j with (Z.to_nat (Z.of_nat j)) at 1 by lia. rewrite av8_nth by lia. rewrite arr_get_blit. unfold arr_inb.
    destruct (Z_lt_le_dec (Z.of_nat j) n) as [C|C].
    + replace ((0 <=? Z.of_nat j) && (Z.of_nat j <? 0 + Z.max 0 n) && ((0 <=? Z.of_nat j) && (Z.of_nat j <? arr_len a))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
      rewrite nth_error_app1 by (rewrite length_firstn, length_skipn, av8_length; lia).
      rewrite nth_error_firstn. destruct (Nat.ltb_spec j (Z.to_nat n)); [|lia].
      rewrite nth_error_skipn. replace (Z.to_nat sofs + j)%nat with (Z.to_nat (sofs + (Z.of_nat j - 0))) by lia.
      rewrite av8_nth by lia. reflexivity.
    + replace ((0 <=? Z.of_nat j) && (Z.of_nat j <? 0 + Z.max 0 n) && ((0 <=? Z.of_nat j) && (Z.of_nat j <? arr_len a))) with false
        by (symmetry; rewrite !andb_false_iff, !Z.ltb_ge; lia).
      rewrite nth_error_app2 by (rewrite length_firstn, length_skipn, av8_length; lia).
      rewrite length_firstn, length_skipn, av8_length, nth_error_skipn.
      replace (Z.to_nat n + (j - Nat.min (Z.to_nat n) (Z.to_nat N - Z.to_nat sofs)))%nat with (Z.to_nat (Z.of_nat j)) by lia.
      rewrite av8_nth by lia. reflexivity.
Qed.
Lemma u8arr_join2z : forall m A (b1 b2 : list byte) n, Z.of_nat (length b1) = n ->
  rw_cells usegs m A [CB (Z.to_nat n) b1] -> u8arr usegs m (A + n) b2 -> u8arr usegs m A (b1 ++ b2).
Proof.
  intros m A b1 b2 n L H1 H2. apply u8arr_app. split; [eapply u8arr_of_rw_cells; exact H1| rewrite L; exact H2].
Qed.
Definition fw_slide4 (s : deflate_state) (more : Z) : deflate_state :=
  set_block_start (set_strstart (set_match_start
    (set_window s (arr_blit (ds_window s) 0 (ds_window s) 32768 (32768 - more)))
    (wrap32 (ds_match_start s - 32768))) (ds_strstart s - 32768)) (ds_block_start s - 32768).
Lemma shm_mach : forall v, 0 <= v < 65536 ->
  Z.land ((Z.b2z (v <? (v - 32768) mod 18446744073709551616) + -1) mod 18446744073709551616) ((v - 32768) mod 18446744073709551616)
  = shm 32768 v.
Proof.
  intros v Hv. rewrite shm_small by lia. destruct (Z.leb_spec 32768 v) as [C|C].
  - rewrite (Z.mod_small (v - 32768)) by lia. replace (v <? v - 32768) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - replace ((v - 32768) mod 18446744073709551616) with (v - 32768 + 18446744073709551616) by (Z.div_mod_to_equations; lia).
    replace (v <? v - 32768 + 18446744073709551616) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0. apply Z.land_0_l.
Qed.
Lemma ms_mach : forall v, le4 (wz (bv_swrap 32 (bv_unsigned (sx32 (wz v)) - 32768))) = le4 (wz (wrap32 (v - 32768))).
Proof.
  intros v. apply le4_wz_mod. unfold sx32. rewrite !Z_to_bv_unsigned, wrap32_mod.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul N.sub N.of_nat Pos.of_succ_nat].
  Z.div_mod_to_equations. lia.
Qed.
Lemma bs_guard : forall bs, - 2 ^ 62 <= bs < 2 ^ 62 ->
  Z.b2z (Z.lxor ((bs mod 18446744073709551616 - 32768) mod 18446744073709551616) 9223372036854775808
         <? Z.lxor (bs mod 18446744073709551616) 9223372036854775808) = 1.
Proof.
  intros bs Hbs. change 9223372036854775808 with (2^63).
  rewrite !zb_lxor_sign by (Z.div_mod_to_equations; lia).
  replace (_ <? _) with true; [reflexivity|]. symmetry. apply Z.ltb_lt.
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  destruct (Z_lt_le_dec bs 0).
  - replace (bs mod 18446744073709551616) with (bs + 18446744073709551616) by (Z.div_mod_to_equations; lia).
    rewrite (Z.mod_small (bs + 18446744073709551616 - 32768)) by lia.
    Z.div_mod_to_equations. lia.
  - rewrite (Z.mod_small bs) by lia.
    destruct (Z_lt_le_dec bs 32768).
    + replace ((bs - 32768) mod 18446744073709551616) with (bs - 32768 + 18446744073709551616) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations. lia.
    + rewrite (Z.mod_small (bs - 32768)) by lia. Z.div_mod_to_equations. lia.
Qed.
Ltac st16u ARR a n A idx v EQ :=
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
Definition shpost1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (pcx A : Z) (a' : arr) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x14 x15 m',
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz 0) (wz A) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch [(A, A + 65536)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' A (u16s (av16 a' 32768)).
Definition shpost2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (pcx A : Z) (a' : arr) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x14 x15 m',
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz A) (wz 0) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch [(A, A + 65536)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' A (u16s (av16 a' 32768)).
Section LOOPS.
Lemma shloop_h : forall (n : nat) (k : Z) (a : arr) (A : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  k = Z.of_nat (S n) -> k <= 32768 ->
  u8arr usegs m A (u16s (av16 a 32768)) -> arr_len a = 32768 -> (forall i, 0 <= i < 32768 -> 0 <= arr_get a i < 65536) ->
  mem_inv usegs m -> 2 <= A -> A + 65536 < 2^62 ->
  evt usegs (shpost1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc Z_SH1X A
                    (slide_hash_loop (Z.to_nat k) a k 32768) m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz k) (wz (A + 2 * k)) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz Z_SH1) fc None m (seg_rom usegs)).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros until m. intros Hk Kle ARR LEN RNG MI A2 AH. unfold Z_SH1.
  assert (K1 : 1 <= k) by lia.
  pose proof (av16_zlength a 32768 ltac:(lia)) as L16.
  pose proof (RNG (k - 1) ltac:(lia)) as Rv.
  pose proof (munch_refl [(A, A + 65536)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  gF.
  ld16 ARR a 32768 A (k - 1) ltac:(exact Rv).
  zs. zstep. zstep. zstep. rewrite (shm_mach (arr_get a (k - 1))) by exact Rv.
  pose proof (shm_range 32768 (arr_get a (k - 1))) as Rs.
  zstep. zs.
  st16u ARR a 32768 A (k - 1) (shm 32768 (arr_get a (k - 1))) ltac:(reflexivity).
  zstep. rewrite (slide_hash_loop_step k a 32768) by exact K1. cbv zeta.
  name_mem m1.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    replace (k - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (wz (A + 2 * k + -2)) with (wz (A + 2 * (k - 1))) by (f_equal; lia).
    replace (wz (k + -1)) with (wz (k - 1)) by (f_equal; lia).
    eapply evt_mono.
    + eapply (IH (n - 1)%nat ltac:(lia) (k - 1) _ A); [lia| lia| exact ARR| rewrite arr_len_set; exact LEN| | assumption| lia| lia].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Rs| apply RNG; exact Hi].
    + intros ms' (x14' & x15' & m2 & -> & MU2 & WM2 & MI2 & ARR2). exists x14', x15', m2.
      split; [reflexivity|]. split; [eapply munch_trans; [exact MU0| exact MU2]|]. split; [eapply wmono_trans; [exact WM0| exact WM2]|].
      split; [exact MI2| exact ARR2].
  -
    replace (k - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    replace (wz (A + 2 * k + -2)) with (wz A) by (f_equal; lia).
    replace (wz (k + -1)) with (wz 0) by (f_equal; lia).
    apply evt_done. unfold shpost1, Z_SH1X. eexists _, _, m1.
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [assumption| exact ARR].
Qed.
Lemma shloop_p : forall (n : nat) (k : Z) (a : arr) (A : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  k = Z.of_nat (S n) -> k <= 32768 ->
  u8arr usegs m A (u16s (av16 a 32768)) -> arr_len a = 32768 -> (forall i, 0 <= i < 32768 -> 0 <= arr_get a i < 65536) ->
  mem_inv usegs m -> 2 <= A -> A + 65536 < 2^62 ->
  evt usegs (shpost2 x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc Z_SH2X A
                    (slide_hash_loop (Z.to_nat k) a k 32768) m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz (A + 2 * k)) (wz k) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz Z_SH2) fc None m (seg_rom usegs)).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros until m. intros Hk Kle ARR LEN RNG MI A2 AH. unfold Z_SH2.
  assert (K1 : 1 <= k) by lia.
  pose proof (av16_zlength a 32768 ltac:(lia)) as L16.
  pose proof (RNG (k - 1) ltac:(lia)) as Rv.
  pose proof (munch_refl [(A, A + 65536)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  gF.
  ld16 ARR a 32768 A (k - 1) ltac:(exact Rv).
  zs. zstep. zstep. zstep. rewrite (shm_mach (arr_get a (k - 1))) by exact Rv.
  pose proof (shm_range 32768 (arr_get a (k - 1))) as Rs.
  zstep. zs.
  st16u ARR a 32768 A (k - 1) (shm 32768 (arr_get a (k - 1))) ltac:(reflexivity).
  zstep. rewrite (slide_hash_loop_step k a 32768) by exact K1. cbv zeta.
  name_mem m1.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    replace (k - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (wz (A + 2 * k + -2)) with (wz (A + 2 * (k - 1))) by (f_equal; lia).
    replace (wz (k + -1)) with (wz (k - 1)) by (f_equal; lia).
    eapply evt_mono.
    + eapply (IH (n - 1)%nat ltac:(lia) (k - 1) _ A); [lia| lia| exact ARR| rewrite arr_len_set; exact LEN| | assumption| lia| lia].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Rs| apply RNG; exact Hi].
    + intros ms' (x14' & x15' & m2 & -> & MU2 & WM2 & MI2 & ARR2). exists x14', x15', m2.
      split; [reflexivity|]. split; [eapply munch_trans; [exact MU0| exact MU2]|]. split; [eapply wmono_trans; [exact WM0| exact WM2]|].
      split; [exact MI2| exact ARR2].
  -
    replace (k - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    replace (wz (A + 2 * k + -2)) with (wz A) by (f_equal; lia).
    replace (wz (k + -1)) with (wz 0) by (f_equal; lia).
    apply evt_done. unfold shpost2, Z_SH2X. eexists _, _, m1.
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [assumption| exact ARR].
Qed.
End LOOPS.
Section SLIDE.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.
End SLIDE.
