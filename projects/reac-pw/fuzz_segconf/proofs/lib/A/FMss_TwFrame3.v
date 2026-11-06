(* lib/A/Prog/TwFrame3.v (RtStr's port, unchanged from cold/c-asan-rt-fmio-n affce6489c8), re-run over the
   local-shadow TW_ASAN, twoway post and memchr wrapper contract (FMss_TwAsan.v, FMss_twoway_strstr_c.v,
   FMss_memchr_wrap_c.v).  Changed lines: the imports, MCW's type and its unfold, and the memchr call's shadow
   premise (shvis_sub of the haystack's, as the line above it does for addressable). *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AsanRTFacts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec Require Import StrFun StrStr StrBytes TwoWay TwSearch TwSearchPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import twoway_strstr_c memchr_c memchr_wrap_c TwFrame1 TwFrame2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import FMss_shv FMss_TwAsan FMss_twoway_strstr_c FMss_memchr_wrap_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require StepFast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac ].
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require AndN.
Import ListNotations.
Open Scope Z_scope.

Section Tw.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
          (m0 : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word).
Hypothesis LO : lo + 4560 <= bv_unsigned sp.
Hypothesis LO0 : 0 <= lo.
Hypothesis TA : TW_ASAN sp a0 a1 m0 hb nb lo.
Hypothesis SEPH : bv_unsigned a0 + Z.of_nat (length hb) + 1 + Z.of_nat (length hs) <= bv_unsigned sp - 4560
                  \/ bv_unsigned sp <= bv_unsigned a0.
Hypothesis SEPN : bv_unsigned a1 + Z.of_nat (length nb) + 1 <= bv_unsigned sp - 4560 \/ bv_unsigned sp <= bv_unsigned a1.
Hypothesis SEPG : GUARD + 8 <= bv_unsigned sp - 4560.
Hypothesis MCW : memchr_wrap_contract_L.

Notation POSTQ := (twoway_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m0).

Lemma tw_exit : forall (m : word -> option byte) (cs : list cell) (bset tbl : list word)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  cells_size cs = 48%nat -> rw_cells rsegs m (bv_unsigned sp + -2240) cs ->
  u64arr rsegs m (bv_unsigned sp + -2192) tbl -> length tbl = 256%nat ->
  u64arr rsegs m (bv_unsigned sp + -144) bset -> length bset = 4%nat ->
  rw_cells rsegs m (bv_unsigned sp + -112)
    [C8 g; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -2240) -> mem_inv rsegs m ->
  munch [(bv_unsigned sp - 4560, bv_unsigned sp)] m0 m -> wmono rsegs m0 m ->
  bytes_at rsegs m (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) ->
  bytes_at rsegs m (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) ->
  x20 = Z_to_bv 64 (strstr_val (bv_unsigned a0) hb nb) ->
  evt rsegs POSTQ
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x9b528) fc None m (seg_rom rsegs)).
Proof.
  intros m cs bset tbl x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         CS FL TB TL BS BL FR ST MI MU WM HH HN ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct (tw_asan_kept _ _ _ _ _ _ _ _ _ _ TA MU WM ltac:(lia) ltac:(lia))
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & SR & _).
  pose proof (stk_release rsegs m lo _ cs ST FL ltac:(lia)) as ST1. rewrite CS in ST1.
  pose proof (tw_stk_release_u64 rsegs m lo _ tbl ST1) as ST2. rewrite TL in ST2.
  replace (bv_unsigned sp + -2240 + Z.of_nat 48) with (bv_unsigned sp + -2192) in ST2 by lia.
  specialize (ST2 TB ltac:(lia)).
  pose proof (tw_stk_release_u64 rsegs m lo _ bset ST2) as ST3. rewrite BL in ST3.
  replace (bv_unsigned sp + -2192 + 8 * Z.of_nat 256) with (bv_unsigned sp + -144) in ST3 by lia.
  specialize (ST3 BS ltac:(lia)).
  replace (bv_unsigned sp + -144 + 8 * Z.of_nat 4) with (bv_unsigned sp + -112) in ST3 by lia.
  clear ST ST1 ST2 FL TB BS.
  rename ST3 into ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold twoway_strstr_post, TWOWAY_STRSTR_K.
  repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.AndN.and_splits; assumption.
Qed.

Variables (c p0 : nat) (bset tbl : list word) (j16 : list byte).
Hypothesis BH : 0 <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat (length hb) + 1 + Z.of_nat (length hs) <= 2^64.
Hypothesis BN : 0 <= bv_unsigned a1 /\ bv_unsigned a1 + Z.of_nat (length nb) + 1 <= 2^64.
Hypothesis NH : ~ In (Z_to_bv 8 0) hb.
Hypothesis NN : ~ In (Z_to_bv 8 0) nb.
Hypothesis L1 : (1 <= length nb)%nat.
Hypothesis LY : (length nb <= length hb)%nat.
Hypothesis CRIT : TW_CRIT (map bv_unsigned nb) c p0.
Hypothesis BSX : BSET (map bv_unsigned nb) bset.
Hypothesis TBX : TBL (map bv_unsigned nb) tbl.
Hypothesis HS : (- (bv_unsigned a0 + Z.of_nat (length hb) + 1)) mod 8 <= Z.of_nat (length hs).
Hypothesis YB : Z.of_nat (length hb) + 2240 <= 2^64.

Notation X := (map bv_unsigned nb).
Notation Y := (map bv_unsigned hb).
Notation L := (length nb).

Lemma LX : length X = L.
Proof. apply length_map. Qed.

Definition MEMOK (m : word -> option byte) : Prop :=
  rw_cells rsegs m (bv_unsigned sp + -2240)
    [CB 16 j16; C8 (Z_to_bv 64 (Z.of_nat (tw_mem0 X c p0))); C8 (Z_to_bv 64 GUARD);
     C8 (Z_to_bv 64 (1 - Z.of_nat c)); C8 (Z_to_bv 64 (bv_unsigned a1 + Z.of_nat c - 1))] /\
  u64arr rsegs m (bv_unsigned sp + -2192) tbl /\ u64arr rsegs m (bv_unsigned sp + -144) bset /\
  rw_cells rsegs m (bv_unsigned sp + -112)
    [C8 g; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (bv_unsigned sp + -2240) /\ mem_inv rsegs m /\
  munch [(bv_unsigned sp - 4560, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\
  bytes_at rsegs m (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) /\
  bytes_at rsegs m (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m GUARD (le8 g).

Notation LS pc r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 m :=
  (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp r5 r6 r7 a1 r9 r10 r11 r12 r13 r14 r15 r16 r17
       (Z_to_bv 64 (Z.of_nat c)) (Z_to_bv 64 (Z.lor (Z.of_nat L) 63)) r20 (Z_to_bv 64 (bv_unsigned sp + -144))
       (Z_to_bv 64 (bv_unsigned a1 + 1)) (Z_to_bv 64 (Z.of_nat L)) (Z_to_bv 64 (Z.of_nat c - 1))
       (Z_to_bv 64 (Z.of_nat (tw_p X c p0))) (Z_to_bv 64 (bv_unsigned sp + -2192)) r27 r28 r29 r30 r31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition KNEXT (m : word -> option byte) (pos mem : nat) (r9 : word) : Prop :=
  forall (pos' mem' : nat) (w10 w11 r1 r5 r6 r7 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 : word),
    tw_body X Y c (tw_p X c p0) (tw_mem0 X c p0) pos mem = TwNext pos' mem' ->
    bv_unsigned w10 = bv_unsigned a0 + Z.of_nat pos' -> bv_unsigned w11 = Z.of_nat mem' ->
    evt rsegs POSTQ (LS 0x9b408 r1 r5 r6 r7 r9 w10 w11 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 m).

Definition KFOUND (m : word -> option byte) (pos mem : nat) : Prop :=
  tw_body X Y c (tw_p X c p0) (tw_mem0 X c p0) pos mem = TwFound pos ->
  forall (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r27 r28 r29 r30 r31 : word),
    evt rsegs POSTQ (LS 0x9b510 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17
                       (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) r27 r28 r29 r30 r31 m).

Lemma tw_lor63 : forall a, 0 <= a -> Z.lor a 63 = 64 * (a / 64) + 63.
Proof.
  intros a Ha. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases n 6) as [Hl|Hg].
  - assert (T : Z.testbit 63 n = true) by (assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5) as E by lia;
      destruct E as [->|[->|[->|[->|[->| ->]]]]]; reflexivity).
    rewrite T, orb_true_r. rewrite <- (Z.mod_pow2_bits_low (64 * (a / 64) + 63) 6 n) by lia.
    replace ((64 * (a / 64) + 63) mod 2 ^ 6) with 63; [symmetry; exact T|].
    change (2 ^ 6) with 64. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. reflexivity.
  - rewrite <- (Z.sub_add 6 n). rewrite <- !Z.shiftr_spec by lia. rewrite !Z.shiftr_div_pow2 by lia.
    change (2 ^ 6) with 64. change (63 / 64) with 0. rewrite Z.testbit_0_l, orb_false_r.
    f_equal. rewrite Z.mul_comm, Z.div_add_l by lia. change (63 / 64) with 0. ring.
Qed.

Lemma tw_lor63_bound : forall a, 0 <= a -> a <= Z.lor a 63 <= a + 63.
Proof. intros a Ha. rewrite tw_lor63 by exact Ha. pose proof (Z.div_mod a 64 ltac:(lia)). pose proof (Z.mod_pos_bound a 64 ltac:(lia)). lia. Qed.

Ltac weq := first [ reflexivity | f_equal; lia
                  | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].
Ltac wsolve := first [ reflexivity | rewrite ?unsigned_lit by lia; lia
                     | rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Ltac tw_facts INV :=
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  pose proof CRIT as (CR1 & CR2 & CR3 & _); rewrite LX in CR1, CR3;
  pose proof INV as (_ & INV2 & _); rewrite LX in INV2;
  pose proof (tw_p_le X c p0 CRIT) as PLE; rewrite LX in PLE;
  pose proof (tw_mem0_le X c p0) as M0LE; rewrite LX in M0LE.

Lemma tw_body_scan' : forall pos mem, inset X (at_ Y (pos + L - 1)) = true ->
  (L - shift_of X (at_ Y (pos + L - 1)) = 0)%nat ->
  tw_body X Y c (tw_p X c p0) (tw_mem0 X c p0) pos mem =
    if (rscan X Y pos (Nat.max c mem) (L - Nat.max c mem) <? L)%nat
    then TwNext (pos + (rscan X Y pos (Nat.max c mem) (L - Nat.max c mem) + 1 - c)) 0
    else if (lscan X Y pos mem c <=? mem)%nat then TwFound pos else TwNext (pos + tw_p X c p0) (tw_mem0 X c p0).
Proof. intros pos mem H K. rewrite <- LX. apply tw_body_scan; rewrite LX; assumption. Qed.

Lemma tw_ls_loop : forall (k : nat) (m : word -> option byte) (pos mem : nat)
    (w10 w11 w12 r1 r5 r6 r7 r9 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  TW_INV X Y pos mem -> (mem = 0 \/ mem = tw_mem0 X c p0)%nat -> (pos + L <= length hb)%nat ->
  MEMOK m -> KNEXT m pos mem r9 -> KFOUND m pos mem ->
  inset X (at_ Y (pos + L - 1)) = true -> (L - shift_of X (at_ Y (pos + L - 1)) = 0)%nat ->
  rscan X Y pos (Nat.max c mem) (L - Nat.max c mem) = L ->
  (k <= c)%nat -> lscan X Y pos mem c = lscan X Y pos mem k ->
  w10 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos + Z.of_nat k - 1) ->
  w11 = Z_to_bv 64 (bv_unsigned a1 + Z.of_nat k - 1) -> w12 = Z_to_bv 64 (Z.of_nat k) ->
  evt rsegs POSTQ (LS 0x9b4d0 r1 r5 r6 r7 r9 w10 w11 w12 r13 r14 r15 r16 r17
                     (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) (Z_to_bv 64 (Z.of_nat mem)) r28 r29 r30 r31 m).
Proof.
  induction k as [|k IH];
    intros m pos mem w10 w11 w12 r1 r5 r6 r7 r9 r13 r14 r15 r16 r17 r28 r29 r30 r31
           INV MEM PL MO KN KF IN SH RS Kc LSC -> -> ->;
    tw_facts INV; pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  - zstep. if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia; cbv iota; [|exfalso; lia].
    apply KF. rewrite tw_body_scan' by assumption. rewrite RS, Nat.ltb_irrefl, LSC.
    cbn [lscan]. replace (0 <=? mem)%nat with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
  - replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
    zstep. if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia; cbv iota.
    + apply KF. rewrite tw_body_scan' by assumption. rewrite RS, Nat.ltb_irrefl, LSC.
      rewrite tw_lscan_stop by lia. replace (S k <=? mem)%nat with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
    + destruct (tw_nth_ex nb k ltac:(lia)) as [bn EN]. destruct (tw_nth_ex hb (pos + k) ltac:(lia)) as [bh EH].
      pose proof (sb_byte_range bn) as RBN. pose proof (sb_byte_range bh) as RBH.
      assert (RN : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a1 + (Z.of_nat k + 1) - 1)) 1 = Some [bn]).
      { apply (sb_rd1 rsegs m (bv_unsigned a1) _ k bn _ HN);
          [rewrite nth_error_app1 by lia; exact EN | rewrite unsigned_lit by lia; lia]. }
      assert (RH : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos + (Z.of_nat k + 1) - 1)) 1 = Some [bh]).
      { apply (sb_rd1 rsegs m (bv_unsigned a0) _ (pos + k) bh _ HH);
          [rewrite nth_error_app1 by lia; exact EH | rewrite unsigned_lit by lia; lia]. }
      pose proof (tw_at_u nb k bn EN) as AN. pose proof (tw_at_u hb (pos + k) bh EH) as AH.
      zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K2; zify_cond K2; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K2 by lia; cbv iota.
      * eapply (IH m pos mem); try eassumption; [lia | | weq | weq | weq].
        rewrite LSC. apply tw_lscan_eq; [lia|]. rewrite AN, AH. lia.
      * zstep. zstep. zstep.
        eapply (KN (pos + tw_p X c p0)%nat (tw_mem0 X c p0)); [ | wsolve | wsolve].
        rewrite tw_body_scan' by assumption. rewrite RS, Nat.ltb_irrefl, LSC.
        rewrite tw_lscan_neq by (rewrite AN, AH; lia).
        replace (S k <=? mem)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
Qed.

Lemma tw_ls_entry : forall (m : word -> option byte) (pos mem : nat)
    (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  TW_INV X Y pos mem -> (mem = 0 \/ mem = tw_mem0 X c p0)%nat -> (pos + L <= length hb)%nat ->
  MEMOK m -> KNEXT m pos mem r9 -> KFOUND m pos mem ->
  inset X (at_ Y (pos + L - 1)) = true -> (L - shift_of X (at_ Y (pos + L - 1)) = 0)%nat ->
  rscan X Y pos (Nat.max c mem) (L - Nat.max c mem) = L ->
  evt rsegs POSTQ (LS 0x9b4c4 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17
                     (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) (Z_to_bv 64 (Z.of_nat mem)) r28 r29 r30 r31 m).
Proof.
  intros m pos mem r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 INV MEM PL MO KN KF IN SH RS.
  tw_facts INV. pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  zstep. zstep. zstep.
  eapply (tw_ls_loop c m pos mem); try eassumption; [lia | reflexivity | weq | weq | weq].
Qed.

Lemma tw_rs_loop : forall (d k : nat) (m : word -> option byte) (pos mem : nat) (b1 : byte)
    (w10 w11 w12 w13 r1 r5 r6 r7 r9 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  (L - k = d)%nat ->
  TW_INV X Y pos mem -> (mem = 0 \/ mem = tw_mem0 X c p0)%nat -> (pos + L <= length hb)%nat ->
  MEMOK m -> KNEXT m pos mem r9 -> KFOUND m pos mem ->
  inset X (at_ Y (pos + L - 1)) = true -> (L - shift_of X (at_ Y (pos + L - 1)) = 0)%nat ->
  (Nat.max c mem <= k < L)%nat -> nth_error nb k = Some b1 ->
  rscan X Y pos (Nat.max c mem) (L - Nat.max c mem) = rscan X Y pos k (L - k) ->
  w10 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos + Z.of_nat k + 1 - Z.of_nat c) ->
  w11 = Z_to_bv 64 (bv_unsigned b1) ->
  w12 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos + Z.of_nat k) ->
  w13 = Z_to_bv 64 (bv_unsigned a1 + 1 + Z.of_nat k) ->
  evt rsegs POSTQ (LS 0x9b4a8 r1 r5 r6 r7 r9 w10 w11 w12 w13 r14 r15 r16 r17
                     (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) (Z_to_bv 64 (Z.of_nat mem)) r28 r29 r30 r31 m).
Proof.
  induction d as [d IH] using lt_wf_ind.
  intros k m pos mem b1 w10 w11 w12 w13 r1 r5 r6 r7 r9 r14 r15 r16 r17 r28 r29 r30 r31
         Hd INV MEM PL MO KN KF IN SH Hk EB RS -> -> -> ->.
  tw_facts INV. pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  destruct (tw_nth_ex hb (pos + k) ltac:(lia)) as [bh EH].
  pose proof (sb_byte_range b1) as RB1. pose proof (sb_byte_range bh) as RBH.
  assert (RH : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos + Z.of_nat k)) 1 = Some [bh]).
  { apply (sb_rd1 rsegs m (bv_unsigned a0) _ (pos + k) bh _ HH);
      [rewrite nth_error_app1 by lia; exact EH | rewrite unsigned_lit by lia; lia]. }
  pose proof (tw_at_u nb k b1 EB) as AN. pose proof (tw_at_u hb (pos + k) bh EH) as AH.
  assert (LK : (L - k = S (L - S k))%nat) by lia.
  zstep. zstep. if_cases K; zify_cond K; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K by lia; cbv iota.
  - zstep. zstep.
    eapply (KN (pos + (k + 1 - c))%nat 0%nat); [ | wsolve | reflexivity].
    rewrite tw_body_scan' by assumption. rewrite RS, LK.
    rewrite tw_rscan_neq by (rewrite AN, AH; lia).
    replace (k <? L)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  - destruct (sb_nth_full nb (S k) ltac:(lia)) as [b2 E2]. pose proof (sb_byte_range b2) as RB2.
    assert (RN : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a1 + 1 + Z.of_nat k)) 1 = Some [b2]).
    { apply (sb_rd1 rsegs m (bv_unsigned a1) _ (S k) b2 _ HN); [exact E2 | rewrite unsigned_lit by lia; lia]. }
    assert (RS2 : rscan X Y pos (Nat.max c mem) (L - Nat.max c mem) = rscan X Y pos (S k) (L - S k)).
    { rewrite RS, LK. apply tw_rscan_eq; [rewrite LX; lia | rewrite AN, AH; lia]. }
    zstep. zstep. zstep. zstep. zstep.
    if_cases K2; zify_cond K2; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K2 by lia; cbv iota.
    + assert (Nk : (S k < L)%nat).
      { destruct (Nat.eq_dec (S k) L) as [E|E]; [|lia]. exfalso. apply K2.
        apply (sb_nth_full_zero nb (S k) b2 NN E2). exact E. }
      rewrite nth_error_app1 in E2 by lia.
      eapply (IH (L - S k)%nat ltac:(lia) (S k) m pos mem b2); try eassumption; [lia | lia | weq | weq | weq | weq].
    + assert (Nk : (S k = L)%nat) by (apply (sb_nth_full_zero nb (S k) b2 NN E2); lia).
      apply tw_ls_entry; try assumption.
      rewrite RS2, Nk, Nat.sub_diag. rewrite <- LX. apply tw_rscan_end.
Qed.

Lemma tw_rs_entry : forall (m : word -> option byte) (pos mem : nat)
    (w13 r1 r5 r6 r7 r9 r10 r11 r12 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  TW_INV X Y pos mem -> (mem = 0 \/ mem = tw_mem0 X c p0)%nat -> (pos + L <= length hb)%nat ->
  MEMOK m -> KNEXT m pos mem r9 -> KFOUND m pos mem ->
  inset X (at_ Y (pos + L - 1)) = true -> (L - shift_of X (at_ Y (pos + L - 1)) = 0)%nat ->
  w13 = Z_to_bv 64 (Z.of_nat (Nat.max c mem)) ->
  evt rsegs POSTQ (LS 0x9b48c r1 r5 r6 r7 r9 r10 r11 r12 w13 r14 r15 r16 r17
                     (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) (Z_to_bv 64 (Z.of_nat mem)) r28 r29 r30 r31 m).
Proof.
  intros m pos mem w13 r1 r5 r6 r7 r9 r10 r11 r12 r14 r15 r16 r17 r28 r29 r30 r31 INV MEM PL MO KN KF IN SH ->.
  tw_facts INV. pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  destruct (tw_nth_ex nb (Nat.max c mem) ltac:(lia)) as [b1 E1]. pose proof (sb_byte_range b1) as RB1.
  pose proof (tw_nz_of_nth nb _ b1 NN E1) as NZ1.
  assert (RN : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a1 + Z.of_nat (Nat.max c mem))) 1 = Some [b1]).
  { apply (sb_rd1 rsegs m (bv_unsigned a1) _ (Nat.max c mem) b1 _ HN);
      [rewrite nth_error_app1 by lia; exact E1 | rewrite unsigned_lit by lia; lia]. }
  zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K by lia; cbv iota;
    [exfalso; lia|].
  zstep. zstep. zstep. zstep.
  eapply (tw_rs_loop _ (Nat.max c mem) m pos mem b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl); try eassumption;
    [lia | reflexivity | weq | weq | weq | weq].
Qed.

Lemma tw_body_skip' : forall pos mem, inset X (at_ Y (pos + L - 1)) = true ->
  (L - shift_of X (at_ Y (pos + L - 1)) <> 0)%nat ->
  tw_body X Y c (tw_p X c p0) (tw_mem0 X c p0) pos mem =
    TwNext (pos + Nat.max (L - shift_of X (at_ Y (pos + L - 1))) mem) 0.
Proof. intros pos mem H K. rewrite <- LX. apply tw_body_skip; rewrite LX; assumption. Qed.

Lemma tw_body_m : forall (m : word -> option byte) (pos mem : nat)
    (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  TW_INV X Y pos mem -> (mem = 0 \/ mem = tw_mem0 X c p0)%nat -> (pos + L <= length hb)%nat ->
  MEMOK m -> KNEXT m pos mem r9 -> KFOUND m pos mem ->
  evt rsegs POSTQ (LS 0x9b448 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17
                     (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) (Z_to_bv 64 (Z.of_nat mem)) r28 r29 r30 r31 m).
Proof.
  intros m pos mem r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 INV MEM PL MO KN KF.
  pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct (tw_nth_ex hb (pos + L - 1) ltac:(lia)) as [bl EL].
  assert (RL : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos + Z.of_nat L + -1)) 1 = Some [bl]).
  { apply (sb_rd1 rsegs m (bv_unsigned a0) _ (pos + L - 1) bl _ HH);
      [rewrite nth_error_app1 by lia; exact EL | rewrite unsigned_lit by lia; lia]. }
  pose proof (sb_byte_range bl) as RBL.
  assert (ABL : at_ Y (pos + L - 1) = bv_unsigned bl) by (apply tw_at_u; exact EL).
  pose proof BSX as [BL4 BSV]. pose proof TBX as [TL256 TBV].
  set (wb := nth (Z.to_nat (bv_unsigned bl / 64)) bset (Z_to_bv 64 0)).
  assert (RB : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + -144 + Z.land (bv_unsigned bl ≫ 3) 24)) 8 = Some (le8 wb)).
  { apply (u64arr_read rsegs m (bv_unsigned sp + -144) bset (bv_unsigned bl / 64) wb _ BSm).
    - apply tw_nth_error_nth. rewrite BL4. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      cbn. apply Z.div_lt_upper_bound; lia.
    - apply Z.div_pos; lia.
    - unfold wa. f_equal. rewrite tw_bs_idx by exact RBL. ring. }
  pose proof (BSV (bv_unsigned bl) RBL) as BIT. fold wb in BIT.
  pose proof (tw_land1_shiftr (bv_unsigned wb) (bv_unsigned bl mod 64) ltac:(apply Z.mod_pos_bound; lia)) as BIT2.
  assert (LB : 0 <= Z.land (bv_unsigned wb ≫ (bv_unsigned bl mod 64)) 1 <= 1).
  { pose proof (Z.land_ones (bv_unsigned wb ≫ (bv_unsigned bl mod 64)) 1 ltac:(lia)) as E.
    change (Z.ones 1) with 1 in E. change (2 ^ 1) with 2 in E. rewrite E.
    pose proof (Z.mod_pos_bound (bv_unsigned wb ≫ (bv_unsigned bl mod 64)) 2 ltac:(lia)). lia. }
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K1; zify_cond K1; rewrite ?Z.mod_small in K1 by lia; cbv iota.
  - assert (NI : inset X (bv_unsigned bl) = false) by (rewrite <- BIT; apply BIT2; lia).
    eapply (KN (pos + L)%nat 0%nat).
    + rewrite <- LX. apply tw_body_notin. rewrite LX, ABL. exact NI.
    + rewrite unsigned_lit by lia. lia.
    + reflexivity.
  - assert (IN : inset X (bv_unsigned bl) = true).
    { rewrite <- BIT. destruct (Z.testbit (bv_unsigned wb) (bv_unsigned bl mod 64)) eqn:E; [reflexivity|].
      exfalso. apply K1. apply BIT2. reflexivity. }
    set (wt := nth (Z.to_nat (bv_unsigned bl)) tbl (Z_to_bv 64 0)).
    assert (RT : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + -2192 + Z.shiftl (bv_unsigned bl) 3)) 8 = Some (le8 wt)).
    { apply (u64arr_read rsegs m (bv_unsigned sp + -2192) tbl (bv_unsigned bl) wt _ TBm).
      - apply tw_nth_error_nth. rewrite TL256. lia.
      - lia.
      - unfold wa. f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. ring. }
    pose proof (TBV (bv_unsigned bl) RBL IN) as TWV. fold wt in TWV.
    pose proof (tw_shift_of_le X (bv_unsigned bl)) as SLE. rewrite LX in SLE.
    pose proof INV as (_ & INV2 & _). rewrite LX in INV2.
    pose proof CRIT as (CR1 & _ & _ & _). rewrite LX in CR1.
    assert (IN' : inset X (at_ Y (pos + L - 1)) = true) by (rewrite ABL; exact IN).
    zstep. zstep. zstep. zstep.
    if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by lia; cbv iota.
    + zstep. zstep. if_cases K3; zify_cond K3; rewrite ?Z.mod_small in K3 by lia; cbv iota.
      * zstep. zstep.
        eapply (KN (pos + Nat.max (L - shift_of X (at_ Y (pos + L - 1))) mem)%nat 0%nat); [ | | reflexivity].
        -- apply tw_body_skip'; [exact IN' | rewrite ABL; lia].
        -- rewrite ABL, Nat.max_l by lia. wsolve.
      * zstep. zstep. zstep. zstep.
        eapply (KN (pos + Nat.max (L - shift_of X (at_ Y (pos + L - 1))) mem)%nat 0%nat); [ | | reflexivity].
        -- apply tw_body_skip'; [exact IN' | rewrite ABL; lia].
        -- rewrite ABL, Nat.max_r by lia. wsolve.
    + assert (SH : (L - shift_of X (at_ Y (pos + L - 1)) = 0)%nat) by (rewrite ABL; lia).
      zstep. zstep. if_cases K4; zify_cond K4; rewrite ?Z.mod_small in K4 by lia; cbv iota.
      * apply tw_rs_entry; try assumption. rewrite Nat.max_l by lia. reflexivity.
      * zstep. apply tw_rs_entry; try assumption. rewrite Nat.max_r by lia. reflexivity.
Qed.

Lemma tw_memok_wcall : forall m m' lo' hi', MEMOK m -> munch [(lo', hi')] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + -2240) ->
  bv_unsigned sp - 4560 <= lo' -> hi' <= bv_unsigned sp - 2240 -> MEMOK m'.
Proof.
  intros m m' lo' hi' (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV) MU' WM' MI' ST' L1' L2'.
  pose proof BSX as [BL4 _]. pose proof TBX as [TL256 _].
  split; [eapply rw_cells_transport; [exact FL | exact MU' | exact WM' |];
          cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I]|].
  split; [eapply u64arr_transport; [exact TBm | exact MU' | exact WM' |];
          cbn [disjoint_from]; rewrite TL256; split; [lia | exact I]|].
  split; [eapply u64arr_transport; [exact BSm | exact MU' | exact WM' |];
          cbn [disjoint_from]; rewrite BL4; split; [lia | exact I]|].
  split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |];
          cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I]|].
  split; [exact ST'|].
  split; [exact MI'|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']];
          unfold sub_fp; cbn [outside]; intros x [Hx _]; split; [lia | exact I]|].
  split; [eapply wmono_trans; eassumption|].
  split; [eapply bytes_at_transport; [exact HH | exact MU' |];
          cbn [disjoint_from]; rewrite length_app; cbn [length]; split; [lia | exact I]|].
  split; [eapply bytes_at_transport; [exact HN | exact MU' |];
          cbn [disjoint_from]; rewrite length_app; cbn [length]; split; [lia | exact I]|].
  eapply bytes_at_transport; [exact GV | exact MU' |].
  cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I].
Qed.

Lemma tw_found_exit : forall (m : word -> option byte) (pos : nat)
    (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r27 r28 r29 r30 r31 : word),
  MEMOK m -> find_first Y X = Some pos ->
  evt rsegs POSTQ (LS 0x9b510 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17
                     (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) r27 r28 r29 r30 r31 m).
Proof.
  intros m pos r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r27 r28 r29 r30 r31 MO FF.
  pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (tw_rd8 _ _ _ _ GV) as RV.
  pose proof BSX as [BL4 _]. pose proof TBX as [TL256 _].
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; cbv iota; [exfalso; lia|].
  eapply tw_exit; try eassumption; [reflexivity|].
  rewrite (tw_sv_some _ hb nb pos FF). reflexivity.
Qed.

Lemma tw_ret0_exit : forall (m : word -> option byte)
    (r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 : word),
  MEMOK m -> find_first Y X = None ->
  evt rsegs POSTQ (LS 0x9b5e0 r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 m).
Proof.
  intros m r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 MO FF.
  pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (tw_rd8 _ _ _ _ GV) as RV.
  pose proof BSX as [BL4 _]. pose proof TBX as [TL256 _].
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; cbv iota; [|exfalso; lia].
  eapply tw_exit; try eassumption; [reflexivity|].
  rewrite (tw_sv_none _ hb nb FF). reflexivity.
Qed.

Lemma tw_loop : forall (d pos mem zo : nat) (m : word -> option byte)
    (w9 w10 w11 r1 r5 r6 r7 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 : word),
  (length hb - pos = d)%nat -> TW_INV X Y pos mem -> (mem = 0 \/ mem = tw_mem0 X c p0)%nat ->
  (pos <= zo <= length hb)%nat -> MEMOK m ->
  bv_unsigned w9 = bv_unsigned a0 + Z.of_nat zo -> bv_unsigned w10 = bv_unsigned a0 + Z.of_nat pos ->
  bv_unsigned w11 = Z.of_nat mem ->
  evt rsegs POSTQ (LS 0x9b408 r1 r5 r6 r7 w9 w10 w11 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 m).
Proof.
  induction d as [d IH] using lt_wf_ind.
  intros pos mem zo m w9 w10 w11 r1 r5 r6 r7 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31
         Hd INV MEM Z MO E9 E10 E11.
  tw_facts INV. pose proof MO as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
  apply tw_word_of in E9, E10, E11. subst w9 w10 w11.
  pose proof (tw_lor63_bound (Z.of_nat L) ltac:(lia)) as LOR.
  assert (L1X : (1 <= length X)%nat) by (rewrite LX; lia).
  assert (BODY : forall m1 r9 (zo' : nat) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    MEMOK m1 -> bv_unsigned r9 = bv_unsigned a0 + Z.of_nat zo' -> (pos + L <= zo' <= length hb)%nat ->
    evt rsegs POSTQ (LS 0x9b448 y1 y5 y6 y7 r9 y10 y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat pos)) (Z_to_bv 64 (Z.of_nat mem)) y28 y29 y30 y31 m1)).
  { intros m1 r9 zo' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MO1 E9 Z'.
    apply tw_body_m; try assumption; [lia | |].
    - intros pos' mem' w10 w11 q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q20 q27 q28 q29 q30 q31 TB E10 E11.
      pose proof (search_ok X Y c p0 L1X CRIT pos mem INV MEM ltac:(rewrite LX, length_map; lia)) as SO.
      rewrite TB in SO. destruct SO as (Hlt & INV' & MEM').
      rewrite LX in Hlt.
      eapply (IH (length hb - pos')%nat ltac:(lia) pos' mem' zo'); try eassumption; [reflexivity | lia].
    - intros TB q1 q5 q6 q7 q9 q10 q11 q12 q13 q14 q15 q16 q17 q27 q28 q29 q30 q31.
      pose proof (search_ok X Y c p0 L1X CRIT pos mem INV MEM ltac:(rewrite LX, length_map; lia)) as SO.
      rewrite TB in SO. destruct SO as (_ & PF).
      apply tw_found_exit; [exact MO1|]. exact (search_found_ok X Y pos mem INV PF). }
  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia; cbv iota.
  - eapply (BODY m _ zo); [exact MO | wsolve | lia].
  - zstep. zstep. zstep. zstep.
    pose proof MCW as MC. unfold memchr_wrap_contract_L, MEMCHR_WRAP, MEMCHR_WRAP_K in MC. cbv zeta in MC.
    assert (BUF : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat zo)))
                    (skipn zo hb ++ Z_to_bv 8 0 :: hs)).
    { rewrite unsigned_lit by lia. rewrite <- tw_skipn_str by lia.
      apply tw_bytes_skip; [exact HH | rewrite length_app; cbn [length]; lia]. }
    assert (OK : memchr_ok (bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat zo))) (bv_unsigned (Z_to_bv 64 0) mod 256)
                   (bv_unsigned (Z_to_bv 64 (Z.lor (Z.of_nat L) 63))) (skipn zo hb ++ Z_to_bv 8 0 :: hs)).
    { rewrite !unsigned_lit by lia. change (0 mod 256) with 0. apply tw_memchr_ok; [exact NH | lia | exact HS]. }
    destruct (tw_asan_kept _ _ _ _ _ _ _ _ _ _ TA MU WM ltac:(lia) ltac:(lia))
      as (LH & LN & ADH & ADN & EH & EN & PH & PN & HL & SPA & AC & SR & RMC & RMP & GCF & CF4 & CF5).
    assert (A0NZ : bv_unsigned a0 + Z.of_nat (length hb) <> 0) by lia.
    pose proof (tw_memchr_n_le (bv_unsigned a0) hb hs zo (Z.lor (Z.of_nat L) 63) NH ltac:(lia) ltac:(lia) A0NZ) as NB.
    eapply evt_cut.
    { eapply MC with (buf := skipn zo hb ++ Z_to_bv 8 0 :: hs) (lo := lo).
      - exact BUF.
      - exact OK.
      - exact MI.
      - rewrite !unsigned_lit by lia. change (0 mod 256) with 0. lia.
      - rewrite !unsigned_lit by lia. change (0 mod 256) with 0.
        apply (AsanRTFacts.addressable_sub m _ _ _ _ ADH); lia.
      - rewrite !unsigned_lit by lia. change (0 mod 256) with 0.
        apply (tw_end_sub m _ _ _ _ ADH EH); lia.
      - rewrite !unsigned_lit by lia. right. apply PH. lia.
      - rewrite !unsigned_lit by lia. rewrite length_app, length_skipn. cbn [length]. lia.
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. lia.
      - exact HL.
      - rewrite unsigned_lit by lia. lia.
      - exact AC.
      - rewrite !unsigned_lit by lia. change (0 mod 256) with 0.
        apply (shvis_sub m _ _ _ _ (proj1 SR)); lia.
      - exact RMC. }
    intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MU' & WM' & MI' & ST' & AC' & SR' & BUF').
    sb_fix_ret.
    unfold MEMCHR_WRAP_K in MU'. rewrite unsigned_lit in MU', ST' by lia.
    assert (MO' : MEMOK m')
      by (eapply tw_memok_wcall; [exact MO | exact MU' | exact WM' | exact MI' | exact ST' | lia | lia]).
    clear FL TBm BSm FR ST MI MU WM HH HN GV BUF' BUF OK ST' AC' SR' MU' WM' MI'
      LH LN ADH ADN EH EN PH PN HL SPA AC SR RMC RMP GCF CF4 CF5 A0NZ NB.
    pose proof MO' as (FL & TBm & BSm & FR & ST & MI & MU & WM & HH & HN & GV).
    rewrite (unsigned_lit (bv_unsigned a0 + Z.of_nat zo)) by lia.
    rewrite (unsigned_lit (Z.lor (Z.of_nat L) 63)) by lia.
    change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0.
    destruct (Z_lt_le_dec (Z.of_nat (length hb - zo)) (Z.lor (Z.of_nat L) 63)) as [HIT|MISS].
    + rewrite (tw_memchr_res_hit (bv_unsigned a0) hb hs zo _ NH ltac:(lia) HIT).
      zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by lia; cbv iota; [exfalso; lia|].
      zstep. zstep. if_cases K3; zify_cond K3; rewrite ?Z.mod_small in K3 by lia; cbv iota; [|exfalso; lia].
      zstep. zstep. if_cases K4; zify_cond K4; rewrite ?Z.mod_small in K4 by lia; cbv iota.
      * apply tw_ret0_exit; [exact MO'|]. apply (search_end_ok X Y pos mem L1X INV). rewrite LX, length_map. lia.
      * eapply (BODY m' _ (length hb)); [exact MO' | wsolve | lia].
    + rewrite (tw_memchr_res_miss (bv_unsigned a0) hb hs zo _ NH ltac:(lia) MISS).
      zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by lia; cbv iota; [|exfalso; lia].
      zstep. zstep. if_cases K3; zify_cond K3; rewrite ?Z.mod_small in K3 by lia; cbv iota; [|exfalso; lia].
      eapply (BODY m' _ (zo + Z.to_nat (Z.lor (Z.of_nat L) 63))%nat); [exact MO' | wsolve | lia].
Qed.

End Tw.
