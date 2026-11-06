From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun StrStr StrBytes TwoWay TwSearch TwMaxSuf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import twoway_strstr_c memcmp_c memcmp twoway_loops_c twoway_loops TwFrame1 TwFrame2 TwFrame3 TwSetup_c.
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

Lemma tw_mcmp_range : forall n (l r : list byte) v, memcmp_model l r n = Some v -> -255 <= v <= 255.
Proof.
  induction n as [|n IH]; intros l r v H.
  - cbn in H. inversion H; subst. lia.
  - destruct l as [|a l]; destruct r as [|b r]; cbn [memcmp_model] in H; try discriminate.
    destruct (bv_unsigned a =? bv_unsigned b); [exact (IH l r v H)|].
    inversion H; subst. pose proof (sb_byte_range a). pose proof (sb_byte_range b). lia.
Qed.

Ltac tw_weq := first [ reflexivity | f_equal; lia
                     | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
                     | rewrite ?unsigned_lit by lia; lia ].

Section Back.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
          (m0 : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word) (bset tbl : list word).
Hypothesis STAT : TW_STATIC sp a0 a1 m0 hb hs nb lo g.
Hypothesis BSX : BSET (map bv_unsigned nb) bset.
Hypothesis TBX : TBL (map bv_unsigned nb) tbl.
Hypothesis LY : (length nb <= length hb)%nat.

Notation POSTQ := (twoway_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m0).
Notation X := (map bv_unsigned nb).
Notation L := (length nb).

Definition FRAME (m : word -> option byte) : Prop :=
  u64arr rsegs m (bv_unsigned sp + -2192) tbl /\ u64arr rsegs m (bv_unsigned sp + -144) bset /\
  rw_cells rsegs m (bv_unsigned sp + -112)
    [C8 g; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (bv_unsigned sp + -2240) /\ mem_inv rsegs m /\
  munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\
  bytes_at rsegs m (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) /\
  bytes_at rsegs m (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m GUARD (le8 g).

Ltac tw_bounds FRM :=
  pose proof STAT as (ST0 & LO & HH0 & NH & HS & HN0 & NN & NE & MI0 & DH & DN & GG0 & GV0 & G1 & G2);
  clear ST0 HH0 HN0 MI0 GG0 GV0;
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  pose proof FRM as (TB & BS & FR & ST & MI & MU & WM & HH & HN & GV);
  pose proof (bytes_at_bound _ _ _ _ HN) as BN; rewrite length_app in BN; cbn [length] in BN;
  pose proof (bytes_at_bound _ _ _ _ HH) as BH; rewrite length_app in BH; cbn [length] in BH;
  pose proof ST as (LO0 & _ & _).

Ltac tw_frame := unfold FRAME; repeat (split; [assumption|]); assumption.

Lemma tw_frame_call : forall m m', FRAME m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> FRAME m'.
Proof.
  intros m m' (TB & BS & FR & ST & MI & MU & WM & HH & HN & GV) MU' WM' MI'.
  split; [eapply u64arr_transport; [exact TB | exact MU' | exact WM' | exact I]|].
  split; [eapply u64arr_transport; [exact BS | exact MU' | exact WM' | exact I]|].
  split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I]|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
  split; [exact MI'|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros z _; exact I|].
  split; [eapply wmono_trans; eassumption|].
  split; [eapply bytes_at_transport; [exact HH | exact MU' | exact I]|].
  split; [eapply bytes_at_transport; [exact HN | exact MU' | exact I]|].
  eapply bytes_at_transport; [exact GV | exact MU' | exact I].
Qed.

Lemma tw_enter : forall (c p0 : nat) (m : word -> option byte) (j16 : list byte)
    (v16 v24 v32 v40 w9 w10 w11 w18 w19 w21 w24 w25 w26 r1 r5 r6 r7 r12 r13 r14 r15 r16 r17 r20 r27 r28 r29 r30 r31 : word),
  TW_CRIT X c p0 ->
  rw_cells rsegs m (bv_unsigned sp + -2240) [CB 16 j16; C8 v16; C8 v24; C8 v32; C8 v40] ->
  FRAME m ->
  v16 = Z_to_bv 64 (Z.of_nat (tw_mem0 X c p0)) -> v24 = Z_to_bv 64 GUARD ->
  v32 = Z_to_bv 64 (1 - Z.of_nat c) -> v40 = Z_to_bv 64 (bv_unsigned a1 + Z.of_nat c - 1) ->
  bv_unsigned w9 = bv_unsigned a0 -> bv_unsigned w10 = bv_unsigned a0 -> bv_unsigned w11 = 0 ->
  w18 = Z_to_bv 64 (Z.of_nat c) -> w19 = Z_to_bv 64 (Z.lor (Z.of_nat L) 63) ->
  w21 = Z_to_bv 64 (bv_unsigned sp + -144) -> w24 = Z_to_bv 64 (Z.of_nat c - 1) ->
  w25 = Z_to_bv 64 (Z.of_nat (tw_p X c p0)) -> w26 = Z_to_bv 64 (bv_unsigned sp + -2192) ->
  evt rsegs POSTQ
    (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp r5 r6 r7 a1 w9 w10 w11 r12 r13 r14 r15 r16 r17
             w18 w19 r20 w21 (Z_to_bv 64 (bv_unsigned a1 + 1)) (Z_to_bv 64 (Z.of_nat L)) w24 w25 w26
             r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x1f4cc) fc None m (seg_rom rsegs)).
Proof.
  intros c p0 m j16 v16 v24 v32 v40 w9 w10 w11 w18 w19 w21 w24 w25 w26 r1 r5 r6 r7 r12 r13 r14 r15 r16 r17 r20
         r27 r28 r29 r30 r31 CRIT FL FRM -> -> -> -> E9 E10 E11 -> -> -> -> -> ->.
  tw_bounds FRM.
  assert (L1 : (1 <= L)%nat) by (destruct nb; [congruence | cbn; lia]).
  eapply (tw_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g LO c p0 bset tbl j16
            ltac:(lia) ltac:(lia) NH NN L1 LY CRIT BSX TBX HS ltac:(lia) (length hb) 0%nat 0%nat 0%nat m);
    [lia | apply tw_inv0; rewrite length_map; exact L1 | left; reflexivity | lia | |
     rewrite E9; lia | rewrite E10; lia | rewrite E11; reflexivity].
  unfold MEMOK. repeat (split; [assumption|]); assumption.
Qed.

Lemma tw_tail : forall (c p0 : nat) (m : word -> option byte) (j16 j16' : list byte)
    (v16 v24 w18 w25 r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r26 r27 r28 r29 r30 r31 : word),
  TW_CRIT X c p0 ->
  rw_cells rsegs m (bv_unsigned sp + -2240) [CB 16 j16; C8 v16; C8 v24; CB 16 j16'] -> FRAME m ->
  v16 = Z_to_bv 64 (Z.of_nat (tw_mem0 X c p0)) -> v24 = Z_to_bv 64 GUARD ->
  w18 = Z_to_bv 64 (Z.of_nat c) -> w25 = Z_to_bv 64 (Z.of_nat (tw_p X c p0)) ->
  evt rsegs POSTQ
    (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp r5 r6 r7 a1 a0 r10 r11 r12 r13 r14 r15 r16 r17
             w18 r19 r20 r21 (Z_to_bv 64 (bv_unsigned a1 + 1)) (Z_to_bv 64 (Z.of_nat L))
             (Z_to_bv 64 (Z.of_nat c - 1)) w25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x1f494) fc None m (seg_rom rsegs)).
Proof.
  intros c p0 m j16 j16' v16 v24 w18 w25 r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r21 r26 r27 r28 r29 r30 r31
         CRIT FL FRM E16 E24 -> ->.
  tw_bounds FRM. clear FRM.
  pose proof CRIT as (CR1 & CR2 & CR3 & _). rewrite length_map in CR1, CR3.
  pose proof (tw_p_le X c p0 CRIT) as PLE. rewrite length_map in PLE.
  pose proof (tw_mem0_le X c p0) as M0LE. rewrite length_map in M0LE.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  eapply (tw_enter c p0); [exact CRIT | exact FL | tw_frame | exact E16 | exact E24 | tw_weq ..].
Qed.

Lemma tw_at9b8 : forall (c p0 : nat) (m : word -> option byte) (j48 : list byte)
    (w24 w25 r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r20 r21 r26 r27 r28 r29 r30 r31 : word),
  TW_CRIT X c p0 -> rw_cells rsegs m (bv_unsigned sp + -2240) [CB 48 j48] -> FRAME m ->
  w24 = Z_to_bv 64 (Z.of_nat c - 1) -> w25 = Z_to_bv 64 (Z.of_nat p0) ->
  evt rsegs POSTQ
    (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp r5 r6 r7 a1 a0 r10 r11 r12 r13 r14 r15 r16 r17
             r18 (Z_to_bv 64 GUARD) r20 r21 (Z_to_bv 64 (bv_unsigned a1 + 1)) (Z_to_bv 64 (Z.of_nat L))
             w24 w25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x1f434) fc None m (seg_rom rsegs)).
Proof.
  intros c p0 m j48 w24 w25 r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r18 r20 r21 r26 r27 r28 r29 r30 r31
         CRIT FL FRM -> ->.
  tw_bounds FRM.
  pose proof CRIT as (CR1 & CR2 & CR3 & _). rewrite length_map in CR1, CR3.
  destruct (tw_memcmp_total nb c p0 ltac:(lia) ltac:(lia)) as [v MV].
  pose proof (tw_memcmp_periodic nb c p0 v ltac:(lia) ltac:(lia) MV) as VP.
  pose proof (tw_mcmp_range _ _ _ _ MV) as VR.
  pose proof memcmp_holds as MC. unfold memcmp_contract, MEMCMP in MC.
  zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut;
    [eapply MC with (ls := nb ++ [Z_to_bv 8 0]) (rs := skipn p0 (nb ++ [Z_to_bv 8 0])) (v := v);
       [ exact HN
       | rewrite unsigned_lit by lia; apply tw_bytes_skip; [exact HN | rewrite length_app; cbn [length]; lia]
       | rewrite unsigned_lit by lia; replace (Z.to_nat (Z.of_nat c - 1 + 1)) with c by lia; exact MV
       | exact MI ] |].
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MU' & WM' & MI' & BL & BR).
  sb_fix_ret.
  pose proof (rw_cells_transport rsegs [] m m' _ _ FL MU' WM' I) as FL'.
  pose proof (tw_frame_call m m' FRM MU' WM' MI') as FRM'.
  clear FL FRM TB BS FR ST MI MU WM HH HN GV BL BR MU' WM' MI'.
  rename FL' into FL.
  pose proof FRM' as (TB & BS & FR & ST & MI & MU & WM & HH & HN & GV). clear FRM'.
  zstep.
  zstep.
  if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia; cbv iota.
  - assert (V0 : v = 0) by (rewrite ?unsigned_lit_wrap in K; Z.div_mod_to_equations; lia).
    pose proof (proj1 VP V0) as PER.
    zstep. zstep.
    eapply (tw_tail c p0); [exact CRIT | exact FL | tw_frame | | reflexivity | tw_weq | ].
    + unfold tw_mem0. rewrite PER, length_map. tw_weq.
    + unfold tw_p. rewrite PER. reflexivity.
  - assert (NPER : tw_periodic X c p0 = false).
    { destruct (tw_periodic X c p0) eqn:E; [|reflexivity]. exfalso. apply K.
      rewrite (proj2 VP eq_refl). reflexivity. }
    assert (C1 : (1 <= c)%nat).
    { destruct c as [|c']; [|lia]. cbn [tw_periodic seq forallb] in NPER. discriminate. }
    assert (LXR : Z.lxor (Z.of_nat c - 1) 18446744073709551615 = 18446744073709551615 - (Z.of_nat c - 1))
      by (apply OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.zb_lxor_ones; lia).
    assert (LMC : (Z.of_nat L + (18446744073709551615 - (Z.of_nat c - 1))) mod 18446744073709551616 = Z.of_nat L - Z.of_nat c).
    { replace (Z.of_nat L + (18446744073709551615 - (Z.of_nat c - 1)))
        with (Z.of_nat L - Z.of_nat c + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    zstep. zstep. zstep. zstep.
    if_cases K2; zify_cond K2; rewrite LXR, LMC in K2; cbv iota.
    + zstep. zstep. zstep.
      eapply (tw_tail c p0); [exact CRIT | exact FL | tw_frame | | reflexivity | tw_weq | ].
      * unfold tw_mem0. rewrite NPER. reflexivity.
      * unfold tw_p. rewrite NPER, length_map. f_equal. lia.
    + zstep. zstep. zstep. zstep.
      eapply (tw_tail c p0); [exact CRIT | exact FL | tw_frame | | reflexivity | tw_weq | ].
      * unfold tw_mem0. rewrite NPER. reflexivity.
      * unfold tw_p. rewrite NPER, length_map, LXR. apply Z_to_bv_eqm.
        replace (Z.of_nat L + (18446744073709551615 - (Z.of_nat c - 1)) + 1)
          with (Z.of_nat L - Z.of_nat c + 1 + 1 * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. f_equal. lia.
Qed.

Lemma tw_at9a4 : forall (c1 p1 c2 p2 : nat) (m : word -> option byte) (j48 : list byte)
    (w10 w11 w24 w25 r1 r5 r6 r7 r12 r13 r14 r15 r16 r17 r18 r20 r21 r26 r27 r28 r29 r30 r31 : word),
  msuf_run Z.gtb X 0 0 1 1 c1 p1 -> msuf_run Z.ltb X 0 0 1 1 c2 p2 ->
  rw_cells rsegs m (bv_unsigned sp + -2240) [CB 48 j48] -> FRAME m ->
  w10 = Z_to_bv 64 (Z.of_nat c1 - 1) -> w11 = Z_to_bv 64 (Z.of_nat p1) ->
  w24 = Z_to_bv 64 (Z.of_nat c2 - 1) -> w25 = Z_to_bv 64 (Z.of_nat p2) ->
  evt rsegs POSTQ
    (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp r5 r6 r7 a1 a0 w10 w11 r12 r13 r14 r15 r16 r17
             r18 (Z_to_bv 64 GUARD) r20 r21 (Z_to_bv 64 (bv_unsigned a1 + 1)) (Z_to_bv 64 (Z.of_nat L))
             w24 w25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x1f420) fc None m (seg_rom rsegs)).
Proof.
  intros c1 p1 c2 p2 m j48 w10 w11 w24 w25 r1 r5 r6 r7 r12 r13 r14 r15 r16 r17 r18 r20 r21 r26 r27 r28 r29 r30 r31
         R1 R2 FL FRM -> -> -> ->.
  tw_bounds FRM.
  assert (L1X : (1 <= length X)%nat) by (rewrite length_map; destruct nb; [congruence | cbn; lia]).
  destruct tw_gt_props as (G1' & G2' & G3'). destruct tw_lt_props as (T1 & T2 & T3).
  destruct (maxsuf_ok Z.gtb X c1 p1 G1' G2' G3' L1X R1) as [[M1 _] _].
  destruct (maxsuf_ok Z.ltb X c2 p2 T1 T2 T3 L1X R2) as [[M2 _] _].
  rewrite length_map in M1, M2.
  pose proof (tw_crit_of_runs X c1 p1 c2 p2 L1X R1 R2) as CR. unfold tw_cut in CR.
  zstep. zstep. zstep.
  if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia; cbv iota.
  - replace (c1 <? c2)%nat with true in CR by (symmetry; apply Nat.ltb_lt; lia). cbn [fst snd] in CR.
    eapply (tw_at9b8 c2 p2); [exact CR | exact FL | exact FRM | tw_weq | tw_weq].
  - zstep. zstep.
    replace (c1 <? c2)%nat with false in CR by (symmetry; apply Nat.ltb_ge; lia). cbn [fst snd] in CR.
    eapply (tw_at9b8 c1 p1); [exact CR | exact FL | exact FRM | tw_weq | tw_weq].
Qed.

Lemma tw_at918 : forall (m : word -> option byte) (j48 : list byte) (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word),
  rw_cells rsegs m (bv_unsigned sp + -2240) [CB 48 j48] -> FRAME m ->
  evt rsegs POSTQ
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 a1 a0
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -144))
             (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 (Z.of_nat L)) x16 x17
             s2 (Z_to_bv 64 GUARD) s4 s5 (Z_to_bv 64 (bv_unsigned a1 + 1)) (Z_to_bv 64 (Z.of_nat L))
             s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1f394) fc None m (seg_rom rsegs)).
Proof.
  intros m j48 x5 x6 x7 x16 x17 x28 x29 x30 x31 FL FRM.
  tw_bounds FRM.
  assert (L1 : (1 <= L)%nat) by (destruct nb; [congruence | cbn; lia]).
  zstep. zstep.
  if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia; cbv iota.
  - zstep. zstep. zstep.
    assert (RS : forall gt, msuf_run gt X 0 0 1 1 0 1) by (intros gt; apply msr_stop; rewrite length_map; lia).
    eapply (tw_at9a4 0 1 0 1)%nat; [apply RS | apply RS | exact FL | exact FRM | tw_weq | tw_weq | tw_weq | tw_weq].
  - zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof msuf1_ok as M1. unfold MSUF1_OK in M1.
    eapply (M1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nb 0%nat 0%nat 1%nat 1%nat);
      [exact HN | rewrite unsigned_lit by lia; reflexivity | lia | lia | lia | lia | ].
    intros c1 p1 y2 y3 y4 y5 y6 R1.
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof msuf2_ok as M2. unfold MSUF2_OK in M2.
    eapply (M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nb 0%nat 0%nat 1%nat 1%nat);
      [exact HN | rewrite unsigned_lit by lia; reflexivity | lia | lia | lia | lia | ].
    intros c2 p2 z2 z3 z4 z5 z6 R2.
    eapply (tw_at9a4 c1 p1 c2 p2); [exact R1 | exact R2 | exact FL | exact FRM | tw_weq | tw_weq | tw_weq | tw_weq].
Qed.

End Back.

Theorem tw_back : TW_BACK.
Proof.
  unfold TW_BACK, AT918.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g STAT
         m j48 bset tbl x5 x6 x7 x16 x17 x28 x29 x30 x31 FL TB TBX BS BSX FR ST MI MU WM HH HN GG GV LY.
  eapply tw_at918.
  all: try eassumption.
  unfold FRAME. repeat (split; [assumption|]); assumption.
Qed.
