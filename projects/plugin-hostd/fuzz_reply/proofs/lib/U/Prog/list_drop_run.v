From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma ldu_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ldu_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma ldu_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma ldu_lxor_hi : forall x, 0 <= x < 2 ^ 63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n) as [<-|N]; [|apply andb_false_r].
  rewrite andb_true_r. destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma ldu_swrap32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2^31) with 2147483648 in Hz. Z.div_mod_to_equations. lia.
Qed.

Ltac ldu_zb H :=
  revert H; rewrite ?Z.shiftl_mul_pow2 by lia; change (2 ^ 4) with 16;
  repeat (rewrite ldu_swrap32 by lia); repeat (rewrite ldu_signed by lia);
  repeat (rewrite ldu_lxor_hi by lia);
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end;
  intro H; cbn in H; first [discriminate | Z.div_mod_to_equations; lia].

Lemma ldu_entry : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo LA V N i : Z) (n c q len : word),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> mem_inv rsegs m ->
  a0 = Z_to_bv 64 LA -> a1 = Z_to_bv 64 i ->
  0 <= LA -> LA + 16 <= 2 ^ 64 -> LA mod 8 = 0 ->
  0 < V -> V mod 8 = 0 -> V + 16 * N <= 2 ^ 63 -> 0 <= i < N ->
  (LA + 16 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= LA) ->
  (V + 16 * N <= bv_unsigned sp - 48 \/ bv_unsigned sp <= V) ->
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V); C4 n; C4 c] ->
  rw_cells rsegs m (V + 16 * i) [C8 q; C8 len] ->
  evt rsegs (fun ms' => exists a1' a2' a3' m' j0,
      ms' = MS (mkR (Z_to_bv 64 0x14dc0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                    (Z_to_bv 64 LA) (Z_to_bv 64 i) q a1' a2' a3' a4 a5 a6 a7
                    (Z_to_bv 64 (16 * i)) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15f4c) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      stk rsegs m' lo (bv_unsigned sp + -48) /\
      rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 n; C4 c] /\
      rw_cells rsegs m' (V + 16 * i) [C8 q; C8 len])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d58) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo LA V N i n c q len ST LO MI -> -> HL0 HL1 HLA HV0 HVA HVN Hi DLA DV RL RV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 zstep.
  zstep. rewrite (ldu_land7 LA HLA).
  zstep. if_false.
  assert (VI8 : (V + 16 * i) mod 8 = 0).
  { rewrite Z.add_mod by lia. rewrite HVA. replace (16 * i) with (i * 2 * 8) by lia. rewrite Z.mod_mul by lia.
    reflexivity. }
  do 6 zstep.
  zstep. if_cases K1; [exfalso; zify_cond K1; ldu_zb K1|].
  do 4 zstep.
  zstep. if_cases K2; [exfalso; zify_cond K2; ldu_zb K2|].
  zstep. if_cases K3; [exfalso; zify_cond K3; ldu_zb K3|].
  zstep.
  match goal with |- context [Z.land ?x 7] =>
    replace (Z.land x 7) with 0 by (rewrite ?Z.shiftl_mul_pow2 by lia; change (2 ^ 4) with 16;
      rewrite ldu_land7; [reflexivity|]; rewrite ?Zmod_mod; first [rewrite Zmod_small by lia | idtac];
      replace (V + i * 16) with (V + 16 * i) by lia; first [exact VI8 | Z.div_mod_to_equations; lia]) end.
  zstep. if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDq : ov_read_bytes rsegs mm (Z_to_bv 64 (V + Z.shiftl i 4)) 8 = Some (le8 q)) end.
  { pose proof (rw_cells_read rsegs _ _ _ 0 (C8 q) RV eq_refl) as R. cbn [csize cbytes Z.of_nat] in R.
    rewrite Z.shiftl_mul_pow2 by lia. replace (V + i * 2 ^ 4) with (V + 16 * i + 0) by lia. exact R. }
  zstep. zstep.
  rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. replace (i * 16) with (16 * i) by lia.
  rewrite (ldu_lxor_hi i) by lia.
  replace (i + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.b2z].
  apply evt_done. do 5 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; eassumption.
Qed.

Ltac ldu_regs_eq :=
  repeat match goal with
  | |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => apply (f_equal (Z_to_bv 64)); solve [Z.div_mod_to_equations; lia]
  | |- _ = _ => first [reflexivity | f_equal]
  end.

Lemma ldu_lor7 : forall x y, x mod 8 = 0 -> y mod 8 = 0 -> Z.land (Z.lor x y) 7 = 0.
Proof.
  intros x y Hx Hy. rewrite Z.land_lor_distr_l. rewrite (ldu_land7 x Hx), (ldu_land7 y Hy). reflexivity.
Qed.

Lemma ldu_mid : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (LA V N i : Z) (c : word),
  s0 = Z_to_bv 64 LA -> s1 = Z_to_bv 64 i -> s2 = Z_to_bv 64 (16 * i) -> s3 = Z_to_bv 64 0 ->
  0 <= LA -> LA + 16 <= 2 ^ 64 ->
  0 < V -> V mod 8 = 0 -> V + 16 * N <= 2 ^ 63 -> 0 <= i < N -> N < 2 ^ 30 ->
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 c] ->
  evt rsegs (fun ms' => exists a3' a4' a5' a6' a7',
      ms' = MS (mkR (Z_to_bv 64 0x14e48) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (16 * i))
                    (Z_to_bv 64 (V + 16 * i)) (Z_to_bv 64 (V + 16 * (i + 1))) (Z_to_bv 64 (16 * (N - i - 1)))
                    a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1dae8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14dc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    LA V N i c -> -> -> -> HL0 HL1 HV0 HVA HVN Hi HN RL.
  assert (VI8 : (V + 16 * i) mod 8 = 0).
  { rewrite Z.add_mod by lia. rewrite HVA. replace (16 * i) with (i * 2 * 8) by lia. rewrite Z.mod_mul by lia.
    reflexivity. }
  assert (VJ8 : (V + 16 * (i + 1)) mod 8 = 0).
  { rewrite Z.add_mod by lia. rewrite HVA. replace (16 * (i + 1)) with ((i + 1) * 2 * 8) by lia.
    rewrite Z.mod_mul by lia. reflexivity. }
  do 4 zstep.
  zstep. if_cases K1; [exfalso; zify_cond K1; ldu_zb K1|].
  do 3 zstep.
  zstep. if_cases K2; [exfalso; zify_cond K2; ldu_zb K2|].
  zstep.
  zstep. if_cases K3; [exfalso; zify_cond K3; ldu_zb K3|].
  do 3 zstep.
  zstep. if_cases K4; [exfalso; zify_cond K4; ldu_zb K4|].
  do 4 zstep.
  zstep. if_cases K5; [exfalso; zify_cond K5; ldu_zb K5|].
  do 3 zstep. rewrite ?(ldu_sx32 N) by lia.
  zstep. if_cases K6; [exfalso; zify_cond K6; ldu_zb K6|].
  do 2 zstep.
  zstep. if_cases K7; [exfalso; zify_cond K7; ldu_zb K7|].
  do 3 zstep.
  zstep.
  match goal with |- context [Z.land (Z.lor ?x ?y) 7] =>
    replace (Z.land (Z.lor x y) 7) with 0 by (symmetry; apply ldu_lor7;
      rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?ldu_swrap32 by lia; change (2 ^ 4) with 16;
      Z.div_mod_to_equations; lia) end.
  zstep. if_false.
  zstep. zstep.
  rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?ldu_swrap32 by lia. change (2 ^ 4) with 16.
  apply evt_done. do 5 eexists.
  ldu_regs_eq.
Qed.

Lemma ldu_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (LA B N : Z) (v c s0v s1v s2v s3v rav : word) (j0 : list byte),
  s0 = Z_to_bv 64 LA -> 0 <= LA -> LA + 16 <= 2 ^ 64 -> sp = Z_to_bv 64 B -> 0 <= B -> B + 48 <= 2 ^ 64 ->
  (LA + 16 <= B \/ B + 48 <= LA) -> 0 < N < 2 ^ 30 -> mem_inv rsegs m ->
  rw_cells rsegs m LA [C8 v; C4 (Z_to_bv 64 N); C4 c] ->
  rw_cells rsegs m B [CB 8 j0; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (fun ms' => exists a0' a1' m',
      ms' = MS (mkR rav (Z_to_bv 64 (B + 48)) gp tp t0 t1 t2 s0v s1v a0' a1' a2 a3 a4 a5 a6 a7
                    s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom rsegs) /\
      munch [(LA + 8, LA + 12)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' LA [C8 v; C4 (Z_to_bv 64 (N - 1)); C4 c] /\
      rw_cells rsegs m' B [CB 8 j0; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e48) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    LA B N v c s0v s1v s2v s3v rav j0 -> HL0 HL1 -> HB0 HB1 DJ HN MI RL FR.
  pose proof (munch_refl [(LA + 8, LA + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. rewrite (ldu_sx32 N) by lia.
  zstep. rewrite ?ldu_swrap32 by lia. try replace (N + -1) with (N - 1) by lia.
  zstep. if_cases K1; [exfalso; zify_cond K1; ldu_zb K1|].
  zstep.
  do 7 zstep.
  apply evt_done. do 3 eexists. split; [ldu_regs_eq|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
