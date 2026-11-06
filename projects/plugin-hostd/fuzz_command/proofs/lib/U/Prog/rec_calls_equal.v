From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcmp_c rec_calls_equal_c.
Import ListNotations.
Open Scope Z_scope.

Lemma calls_at_transport : forall mc mc' lo hi A es,
  calls_at mc lo hi A es -> munch [(lo, hi)] mc mc' -> calls_at mc' lo hi A es.
Proof.
  intros mc mc' lo hi A es [HL H] MU. split; [exact HL|].
  intros i e Hi. destruct (H i e Hi) as (Hf & Hn & HB & HAp & HA).
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app, !length_le4 in BB.
  unfold apart in HAp.
  split; [exact Hf|]. split; [exact Hn|]. split.
  - eapply bytes_at_transport; [exact HB | exact MU |]. cbn [disjoint_from].
    rewrite length_app, !length_le4. split; [lia | exact I].
  - split; [exact HAp|]. intros k p Hk. destruct (HA k p Hk) as (HS & HP & HZ & HPa).
    assert (Kk : (k < length (snd e))%nat) by (apply nth_error_Some; congruence).
    unfold apart in HPa.
    split; [|split; [|split]].
    + eapply bytes_at_transport; [exact HS | exact MU |]. cbn [disjoint_from].
      rewrite length_le8. split; [lia | exact I].
    + eapply bytes_at_transport; [exact HP | exact MU |]. cbn [disjoint_from].
      rewrite length_app. cbn [length]. split; [lia | exact I].
    + exact HZ.
    + exact HPa.
Qed.

Lemma firstn4_le4 : forall (x : word) l, firstn 4 (le4 x ++ l) = le4 x.
Proof.
  intros x l. rewrite firstn_app, length_le4, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. rewrite length_le4. lia.
Qed.

Lemma skipn4_le4 : forall (x : word) l, skipn 4 (le4 x ++ l) = l.
Proof.
  intros x l. rewrite skipn_app, skipn_all2 by (rewrite length_le4; lia). rewrite length_le4, Nat.sub_diag.
  reflexivity.
Qed.

Lemma entry_read : forall mc lo hi E e,
  entry_at mc lo hi E e ->
  ov_read_bytes rsegs mc (wa E) 4 = Some (le4 (Z_to_bv 64 (fst e))) /\
  ov_read_bytes rsegs mc (wa (E + 4)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (snd e))))).
Proof.
  intros mc lo hi E e (_ & _ & HB & _ & _). split.
  - replace (wa E) with (wa (E + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs mc E _ 0 4 HB) by (rewrite ?length_app, ?length_le4; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O, firstn4_le4. reflexivity.
  - rewrite (bytes_at_read rsegs mc E _ 4 4 HB) by (rewrite ?length_app, ?length_le4; lia).
    change (Z.to_nat 4) with 4%nat. rewrite skipn4_le4. f_equal; apply firstn_all2; rewrite ?length_le4; lia.
Qed.

Lemma arg_read : forall mc lo hi E k p,
  arg_at mc lo hi E k p ->
  ov_read_bytes rsegs mc (wa (E + 8 + 8 * Z.of_nat k)) 8 = Some (le8 (fst p)).
Proof.
  intros mc lo hi E k p (HS & _ & _ & _).
  replace (wa (E + 8 + 8 * Z.of_nat k)) with (wa (E + 8 + 8 * Z.of_nat k + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs mc _ _ 0 8 HS) by (rewrite ?length_le8; lia).
  change (Z.to_nat 0) with 0%nat. rewrite skipn_O. f_equal; apply firstn_all2; rewrite ?length_le8; lia.
Qed.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_lit_signed : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in Hx, Hy.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma cstr_eqb_spec : forall x y, cstr_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold cstr_eqb.
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned y)) as [E|E]; split; intros H;
    try discriminate; try reflexivity.
  - revert y E H. induction x as [|u x IH]; intros [|w y] E _; cbn in E; try discriminate; [reflexivity|].
    injection E as Eu Ex. f_equal; [apply bv_eq; exact Eu | apply IH; [exact Ex | reflexivity]].
  - subst y. contradiction (E eq_refl).
Qed.

Lemma args_eqb_len : forall x y, args_eqb x y = true -> length x = length y.
Proof.
  induction x as [|p x IH]; intros [|q y] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [_ H]. cbn. f_equal. apply IH. exact H.
Qed.

Lemma bv_eqb_true : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma skipn_succ_cons : forall {X} (l rest : list X) n r, skipn n l = r :: rest -> skipn (S n) l = rest.
Proof.
  intros X l. induction l as [|y l IH]; intros rest n r H; destruct n; cbn in *; try discriminate.
  - inversion H; reflexivity.
  - eapply IH. exact H.
Qed.

Lemma skipn_nth : forall {X} (l rest : list X) n r, skipn n l = r :: rest -> nth_error l n = Some r.
Proof.
  intros X l. induction l as [|y l IH]; intros rest n r H; destruct n; cbn in *; try discriminate.
  - inversion H; reflexivity.
  - eapply IH. exact H.
Qed.

Lemma addr56 : forall (x : word) (i : nat), (i <= 16)%nat ->
  Z_to_bv 64 (bv_unsigned x + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 6)) -
                               bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 3))))
  = Z_to_bv 64 (bv_unsigned x + 56 * Z.of_nat i).
Proof.
  intros x i Hi. rewrite (unsigned_lit (Z.of_nat i)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. change (2^3) with 8.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma calls_eqb_len : forall x y, calls_eqb x y = true -> length x = length y.
Proof.
  induction x as [|e x IH]; intros [|f y] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [_ H]. cbn. f_equal. apply IH. exact H.
Qed.

Lemma skipn_len_nil : forall {X} (l : list X) n, length l = n -> skipn n l = [].
Proof. intros X l n <-. apply skipn_all. Qed.

Lemma snez1 : forall x : word, bv_unsigned x <> 0 -> v_sltu (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof.
  intros x H. pose proof (zr_word x) as R. unfold inr64 in R.
  rewrite v_sltu_b2z, (unsigned_lit 0) by lia.
  replace (0 <? bv_unsigned x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma snez1' : forall x : word, bv_unsigned x <> 0 -> Sem.alu64 Instr.ALU_SLTU (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof. intros x H. rewrite alu_sltu. apply snez1. exact H. Qed.

Lemma aligned1 : forall x : word, bv_unsigned x mod 8 = 0 ->
  v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned x) 7)) 1 = Z_to_bv 64 1.
Proof.
  intros x H. rewrite v_sltiu_b2z. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2^3) with 8. rewrite H. reflexivity.
Qed.

Lemma land11 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned (Z_to_bv 64 1))) = Z_to_bv 64 1.
Proof. reflexivity. Qed.

Lemma seqz0 : forall X, 0 < X < 2^64 -> v_sltiu (Z_to_bv 64 X) 1 = Z_to_bv 64 0.
Proof.
  intros X HX. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (X <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma shl3 : forall k, (k <= 16)%nat ->
  Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat k))) 3 = 8 * Z.of_nat k.
Proof.
  intros k Hk. rewrite (unsigned_lit (Z.of_nat k)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2^3) with 8. lia.
Qed.

Lemma not_val : forall X, 0 <= X < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 X)) 18446744073709551615)) = 2^64 - 1 - X.
Proof.
  intros X HX. rewrite (unsigned_lit X) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia.
Qed.

Section Loop.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a b : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (lo : Z) (ca cb : list rc_entry).
Hypothesis STRCMP : strcmp_contract.
Hypothesis LO : lo + 128 <= bv_unsigned sp.

Definition calls_post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if calls_eqb ca cb then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Lemma calls_exit24 : forall mc junk r rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c s8c s9c
    s10c s11c t3c t4c t5c t6c,
  rw_cells rsegs mc (bv_unsigned sp + -128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv rsegs mc -> munch [(bv_unsigned sp + -128, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -128) ->
  r = (if calls_eqb ca cb then 1 else 0) ->
  evt rsegs calls_post
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0c t1c t2c (Z_to_bv 64 r) s1c
             a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c t3c t4c t5c t6c)
        F (Z_to_bv 64 0x15ef0) fc None mc (seg_rom rsegs)).
Proof.
  intros mc junk r rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c
    t3c t4c t5c t6c FR MI MU WM ST Hr. subst r.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 15 step.
  release_frame FR ST (bv_unsigned sp).
  step.
  finish.
Qed.

Lemma calls_exit3 : forall mc f0 f8 f16 r rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c
    s8c s9c s10c s11c t3c t4c t5c t6c,
  rw_cells rsegs mc (bv_unsigned sp + -128)
    [C8 f0; C8 f8; C8 f16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv rsegs mc -> munch [(bv_unsigned sp + -128, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -128) ->
  r = (if calls_eqb ca cb then 1 else 0) ->
  evt rsegs calls_post
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0c t1c t2c (Z_to_bv 64 r) s1c
             a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c t3c t4c t5c t6c)
        F (Z_to_bv 64 0x15ef0) fc None mc (seg_rom rsegs)).
Proof.
  intros mc f0 f8 f16 r rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c
    t3c t4c t5c t6c FR MI MU WM ST Hr. subst r.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 15 step.
  release_frame FR ST (bv_unsigned sp).
  step.
  finish.
Qed.

Lemma calls_outer : forall restA restB i mc f0 f8 f16 rac t0c t1c t2c a0c a1c a2c a4c a5c a6c a7c s5c s6c s8c s9c s11c
    t3c t4c t5c t6c,
  skipn i ca = restA -> skipn i cb = restB -> restA <> [] -> length ca = length cb ->
  calls_eqb ca cb = calls_eqb restA restB ->
  calls_at mc (bv_unsigned sp + -128) (bv_unsigned sp) (bv_unsigned a) ca ->
  calls_at mc (bv_unsigned sp + -128) (bv_unsigned sp) (bv_unsigned b) cb ->
  bv_unsigned a <> 0 -> bv_unsigned b <> 0 ->
  bv_unsigned f0 = 1 -> bv_unsigned f8 = 1 -> bv_unsigned f16 = 1 ->
  rw_cells rsegs mc (bv_unsigned sp + -128)
    [C8 f0; C8 f8; C8 f16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv rsegs mc -> munch [(bv_unsigned sp + -128, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -128) ->
  evt rsegs calls_post
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0c t1c t2c (Z_to_bv 64 1) b
             a0c a1c a2c (Z_to_bv 64 1) a4c a5c a6c a7c (Z_to_bv 64 (Z.of_nat (length ca))) a (Z_to_bv 64 (Z.of_nat i))
             s5c s6c (Z_to_bv 64 (bv_unsigned b + 8 + 56 * Z.of_nat i)) s8c s9c
             (Z_to_bv 64 (bv_unsigned a + 8 + 56 * Z.of_nat i)) s11c t3c t4c t5c t6c)
        F (Z_to_bv 64 0x15e34) fc None mc (seg_rom rsegs)).
Proof.
  induction restA as [|ea restA IH];
    intros restB i mc f0 f8 f16 rac t0c t1c t2c a0c a1c a2c a4c a5c a6c a7c s5c s6c s8c s9c s11c t3c t4c t5c t6c
      HsA HsB Hne HL Heq HCA HCB NZA NZB H0 H8 H16 FR MI MU WM ST; [congruence|].
  destruct restB as [|eb restB].
  { exfalso. pose proof (f_equal (@length _) HsA) as L1. pose proof (f_equal (@length _) HsB) as L2.
    rewrite length_skipn in L1, L2. cbn [length] in L1, L2. lia. }
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a) as Ra. unfold inr64 in Ra.
  pose proof (zr_word b) as Rb. unfold inr64 in Rb.
  pose proof (skipn_nth _ _ _ _ HsA) as NA. pose proof (skipn_nth _ _ _ _ HsB) as NB.
  pose proof (skipn_succ_cons _ _ _ _ HsA) as HsA'. pose proof (skipn_succ_cons _ _ _ _ HsB) as HsB'.
  assert (Hi : (i < length ca)%nat) by (apply nth_error_Some; congruence).
  pose proof (proj1 HCA) as LA.
  pose proof (proj2 HCA i ea NA) as EA. pose proof (proj2 HCB i eb NB) as EB.
  assert (LRA : (S i + length restA = length ca)%nat).
  { pose proof (f_equal (@length _) HsA) as L1. rewrite length_skipn in L1. cbn [length] in L1. lia. }
  assert (LRB : (S i + length restB = length cb)%nat).
  { pose proof (f_equal (@length _) HsB) as L1. rewrite length_skipn in L1. cbn [length] in L1. lia. }
  assert (NEXT : forall rac' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s9' s11' t3' t4' t5' t6',
    calls_eqb ca cb = calls_eqb restA restB ->
    evt rsegs calls_post
      (MS (mkR rac' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) b
               a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat (length ca))) a (Z_to_bv 64 (Z.of_nat i))
               s5' (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned b + 8 + 56 * Z.of_nat i)) s8' s9'
               (Z_to_bv 64 (bv_unsigned a + 8 + 56 * Z.of_nat i)) s11' t3' t4' t5' t6')
          F (Z_to_bv 64 0x15ed4) fc None mc (seg_rom rsegs))).
  { intros rac' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s9' s11' t3' t4' t5' t6' Heq'.
    do 5 step.
    rewrite eqb_lit_signed by lia.
    destruct (Z.eqb_spec (Z.of_nat i + 1) (Z.of_nat (length ca))) as [EI|EI]; cbn [negb].
    - step. eapply calls_exit3; try eassumption.
      rewrite Heq'. destruct restA; [|cbn [length] in LRA; lia]. destruct restB; [|cbn [length] in LRB; lia].
      reflexivity.
    - replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
      replace (Z_to_bv 64 (bv_unsigned b + 8 + 56 * Z.of_nat i + 56))
        with (Z_to_bv 64 (bv_unsigned b + 8 + 56 * Z.of_nat (S i))) by (f_equal; lia).
      replace (Z_to_bv 64 (bv_unsigned a + 8 + 56 * Z.of_nat i + 56))
        with (Z_to_bv 64 (bv_unsigned a + 8 + 56 * Z.of_nat (S i))) by (f_equal; lia).
      eapply (IH restB (S i) mc f0 f8 f16); try eassumption.
      destruct restA; [cbn [length] in LRA; lia | discriminate]. }
  destruct (entry_read _ _ _ _ _ EA) as [RA1 RA2].
  destruct (entry_read _ _ _ _ _ EB) as [RB1 RB2].
  destruct EA as (FA & NLA & BA & _ & ARGA). destruct EB as (FB & NLB & BB & _ & ARGB).
  pose proof (bytes_at_bound _ _ _ _ BA) as BBA. pose proof (bytes_at_bound _ _ _ _ BB) as BBB.
  rewrite length_app, !length_le4 in BBA, BBB.
  do 4 step.
  rewrite (addr56 a i) by lia.
  step.
  rewrite seqz0 by lia.
  step. if_false.
  step.
  replace (bv_ltu (Z_to_bv 64 (bv_unsigned a + 56 * Z.of_nat i)) a) with false
    by (symmetry; unfold bv_ltu; rewrite unsigned_lit by lia; apply Z.ltb_ge; lia).
  cbv iota.
  step. step.
  replace (bv_eqb f16 (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; rewrite H16; reflexivity).
  cbv iota.
  step. step.
  rewrite (addr56 b i) by lia.
  step.
  rewrite seqz0 by lia.
  step. step.
  replace (bv_eqb f8 (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; rewrite H8; reflexivity).
  cbv iota.
  step.
  replace (bv_ltu (Z_to_bv 64 (bv_unsigned b + 56 * Z.of_nat i)) b) with false
    by (symmetry; unfold bv_ltu; rewrite unsigned_lit by lia; apply Z.ltb_ge; lia).
  cbv iota.
  step. step.
  replace (bv_eqb f0 (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; rewrite H0; reflexivity).
  cbv iota.
  step. step.
  rewrite ?sx32_lit by lia.
  step.
  rewrite eqb_lit_signed by lia.
  destruct (Z.eqb_spec (fst ea) (fst eb)) as [EF|EF]; cbn [negb].
  2: { step. eapply calls_exit3; try eassumption.
       rewrite Heq. cbn [calls_eqb]. rewrite (proj2 (Z.eqb_neq _ _) EF). reflexivity. }
  step. step.
  rewrite ?sx32_lit by lia.
  step.
  rewrite eqb_lit_signed by lia.
  destruct (Z.eqb_spec (Z.of_nat (length (snd ea))) (Z.of_nat (length (snd eb)))) as [EN|EN]; cbn [negb].
  2: { step. eapply calls_exit3; try eassumption.
       rewrite Heq. cbn [calls_eqb].
       destruct (args_eqb (snd ea) (snd eb)) eqn:EAB; [apply args_eqb_len in EAB; lia|].
       rewrite andb_false_r. reflexivity. }
  assert (INNER : forall restP restQ k rac' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      (w5 w8 w9 : word),
    skipn k (snd ea) = restP -> skipn k (snd eb) = restQ -> restP <> [] ->
    calls_eqb ca cb = args_eqb restP restQ && calls_eqb restA restB ->
    bv_unsigned w5 = 8 * Z.of_nat (length (snd ea)) ->
    bv_unsigned w8 = 2^64 - 1 - (bv_unsigned a + 56 * Z.of_nat i + 8) ->
    bv_unsigned w9 = 2^64 - 1 - (bv_unsigned b + 56 * Z.of_nat i + 8) ->
    evt rsegs calls_post
      (MS (mkR rac' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) b
               a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat (length ca))) a (Z_to_bv 64 (Z.of_nat i))
               w5 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned b + 8 + 56 * Z.of_nat i)) w8 w9
               (Z_to_bv 64 (bv_unsigned a + 8 + 56 * Z.of_nat i)) (Z_to_bv 64 (8 * Z.of_nat k)) t3' t4' t5' t6')
          F (Z_to_bv 64 0x15eac) fc None mc (seg_rom rsegs))).
  { induction restP as [|p restP IHP];
      intros restQ k rac' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w5 w8 w9 HP HQ HneP HeqP
        H5 H8' H9'; [congruence|].
    assert (LP : (S k + length restP = length (snd ea))%nat).
    { pose proof (f_equal (@length _) HP) as L1. rewrite length_skipn in L1. cbn [length] in L1.
      pose proof (nth_error_Some (snd ea) k) as NS. rewrite (skipn_nth _ _ _ _ HP) in NS.
      assert (k < length (snd ea))%nat by (apply NS; discriminate). lia. }
    destruct restQ as [|q restQ].
    { exfalso. pose proof (f_equal (@length _) HQ) as L1. rewrite length_skipn in L1. cbn [length] in L1. lia. }
    pose proof (skipn_nth _ _ _ _ HP) as NP'. pose proof (skipn_nth _ _ _ _ HQ) as NQ'.
    pose proof (skipn_succ_cons _ _ _ _ HP) as HP'. pose proof (skipn_succ_cons _ _ _ _ HQ) as HQ'.
    assert (LQ : (S k + length restQ = length (snd eb))%nat).
    { pose proof (f_equal (@length _) HQ) as L1. rewrite length_skipn in L1. cbn [length] in L1. lia. }
    pose proof (arg_read mc _ _ _ k p (ARGA k p NP')) as RP.
    pose proof (arg_read mc _ _ _ k q (ARGB k q NQ')) as RQ.
    destruct (ARGA k p NP') as (SA & PA & ZA & _). destruct (ARGB k q NQ') as (SB & PB & ZB & _).
    pose proof (bytes_at_bound _ _ _ _ SA) as BSA. pose proof (bytes_at_bound _ _ _ _ SB) as BSB.
    rewrite length_le8 in BSA, BSB.
    replace (bv_unsigned a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k)
      with (bv_unsigned a + 8 + 56 * Z.of_nat i + 8 * Z.of_nat k) in RP, BSA by lia.
    replace (bv_unsigned b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k)
      with (bv_unsigned b + 8 + 56 * Z.of_nat i + 8 * Z.of_nat k) in RQ, BSB by lia.
    step.
    replace (bv_ltu w8 (Z_to_bv 64 (8 * Z.of_nat k))) with false
      by (symmetry; unfold bv_ltu; rewrite H8', unsigned_lit by lia; apply Z.ltb_ge; lia).
    cbv iota.
    step.
    replace (bv_ltu w9 (Z_to_bv 64 (8 * Z.of_nat k))) with false
      by (symmetry; unfold bv_ltu; rewrite H9', unsigned_lit by lia; apply Z.ltb_ge; lia).
    cbv iota.
    step. step. step. step. step.
    eapply evt_cut.
    { eapply STRCMP with (sx := snd p) (sy := snd q); [exact PA | exact ZA | exact PB | exact ZB]. }
    intros ms' (r & x11 & x12 & x13 & -> & Hr).
    replace (ret_pc (Z_to_bv 64 0x15ec8)) with (Z_to_bv 64 0x15ec8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step.
    destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER; cbn [negb].
    - apply bv_eqb_true in ER. apply Hr in ER.
      step. step.
      unfold bv_eqb. rewrite H5, unsigned_lit by lia.
      destruct (Z.eqb_spec (8 * Z.of_nat (length (snd ea))) (8 * Z.of_nat k + 8)) as [EZ|EZ]; cbn [negb].
      + apply NEXT. rewrite HeqP. cbn [args_eqb]. rewrite (proj2 (cstr_eqb_spec _ _) ER).
        destruct restP; [|cbn [length] in LP; lia]. destruct restQ; [|cbn [length] in LQ; lia]. reflexivity.
      + replace (Z_to_bv 64 (8 * Z.of_nat k + 8)) with (Z_to_bv 64 (8 * Z.of_nat (S k))) by (f_equal; lia).
        eapply (IHP restQ (S k)); try eassumption.
        * destruct restP; [cbn [length] in LP; lia | discriminate].
        * rewrite HeqP. cbn [args_eqb]. rewrite (proj2 (cstr_eqb_spec _ _) ER). reflexivity.
    - step. eapply calls_exit3; try eassumption.
      rewrite HeqP. cbn [args_eqb].
      destruct (cstr_eqb (snd p) (snd q)) eqn:EC; [|reflexivity].
      apply cstr_eqb_spec, Hr in EC. subst r. vm_compute in ER. discriminate ER. }
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (Z.of_nat (length (snd ea)) <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r.
  destruct (Z.ltb_spec 0 (Z.of_nat (length (snd ea)))) as [NP0|NP0]; cbn [negb].
  - assert (S0A : bv_unsigned a + 56 * Z.of_nat i + 8 + 8 <= 2^64).
    { destruct (nth_error (snd ea) 0) as [pa0|] eqn:N0; [| apply nth_error_None in N0; lia].
      destruct (ARGA 0%nat pa0 N0) as (SA0 & _).
      apply bytes_at_bound in SA0. rewrite length_le8 in SA0. lia. }
    assert (S0B : bv_unsigned b + 56 * Z.of_nat i + 8 + 8 <= 2^64).
    { destruct (nth_error (snd eb) 0) as [pb0|] eqn:N0; [| apply nth_error_None in N0; lia].
      destruct (ARGB 0%nat pb0 N0) as (SB0 & _).
      apply bytes_at_bound in SB0. rewrite length_le8 in SB0. lia. }
    do 6 step.
    eapply (INNER (snd ea) (snd eb) 0%nat).
    + reflexivity.
    + reflexivity.
    + destruct (snd ea); [cbn [length] in NP0; lia | discriminate].
    + rewrite Heq. cbn [calls_eqb]. rewrite EF, Z.eqb_refl. reflexivity.
    + rewrite (shl3 (length (snd ea))) by lia. rewrite unsigned_lit by lia. lia.
    + apply not_val. lia.
    + apply not_val. lia.
  - apply NEXT. rewrite Heq. cbn [calls_eqb]. rewrite EF, Z.eqb_refl.
    destruct (snd ea) eqn:SA; [|cbn [length] in NP0; lia].
    destruct (snd eb) eqn:SB; [|cbn [length] in EN; lia]. reflexivity.
Qed.

End Loop.

Theorem rec_calls_equal_holds : strcmp_contract -> rec_calls_equal_contract.
Proof.
  intros STRCMP. unfold rec_calls_equal_contract, REC_CALLS_EQUAL, REC_CALLS_EQUAL_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ca cb
    MI ST LO -> -> HA HB AA AB.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (proj1 HA) as LA. pose proof (proj1 HB) as LB.
  carve_frame 128%nat ST.
  do 15 step.
  rewrite eqb_lit_signed by lia.
  destruct (Z.eqb_spec (Z.of_nat (length ca)) (Z.of_nat (length cb))) as [EL|EL]; cbn [negb].
  2: { step.
       eapply (calls_exit24 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo ca cb LO); try eassumption.
       destruct (calls_eqb ca cb) eqn:E; [apply calls_eqb_len in E; lia | reflexivity]. }
  step. step. step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (Z.of_nat (length ca) <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r.
  destruct (Z.ltb_spec 0 (Z.of_nat (length ca))) as [NP0|NP0]; cbn [negb].
  2: { eapply (calls_exit24 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo ca cb LO); try eassumption.
       destruct ca; [|cbn [length] in NP0; lia]. destruct cb; [|cbn [length] in EL; lia]. reflexivity. }
  destruct (AA ltac:(lia)) as [NZA ALA]. destruct (AB ltac:(lia)) as [NZB ALB].
  do 11 step.
  rewrite (snez1 a0 NZA), (snez1' a2 NZB), (aligned1 a0 ALA), (aligned1 a2 ALB), land11.
  do 5 step.
  pose proof (calls_at_transport _ _ _ _ _ _ HA MU) as HA'.
  pose proof (calls_at_transport _ _ _ _ _ _ HB MU) as HB'.
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat 0)) by reflexivity.
  replace (Z_to_bv 64 (bv_unsigned a2 + 8)) with (Z_to_bv 64 (bv_unsigned a2 + 8 + 56 * Z.of_nat 0))
    by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned a0 + 8)) with (Z_to_bv 64 (bv_unsigned a0 + 8 + 56 * Z.of_nat 0))
    by (f_equal; lia).
  eapply (calls_outer ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a2 F fc m lo ca cb STRCMP LO ca cb 0%nat).
  all: first [ reflexivity | eassumption | lia | idtac ].
  all: first [ reflexivity | (destruct ca; [cbn [length] in NP0; lia | discriminate]) ].
Qed.
