From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require write_uint_c write_uint.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import write_uint_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.write_uint_c(
  write_uint_dg, write_uint_lsd, write_uint_D, write_uint_n).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.write_uint(
  wu_q, wu_t1, wu_dig, wu_lsd_lt10, wu_lsd_ge10, wu_lsd5, wu_n_eq, wu_nth_rev).
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Local Ltac rng := rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.

Local Ltac ul :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by rng end.

Local Ltac bcond :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); bcond
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); bcond
  | _ => first [ apply Z.eqb_eq; rng | apply Z.eqb_neq; rng | apply Z.ltb_lt; rng | apply Z.ltb_ge; rng ]
  end.

Local Ltac br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [ cbv iota | symmetry; unfold_cond; ul; fold_lit_ux; bcond ]
  end.

Lemma wu_dec : forall i, 0 <= i < 5 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (- i)) + -1)) = Z_to_bv 64 (- (i + 1)).
Proof.
  intros i Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct H as [-> | [-> | [-> | [-> | ->]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma wu_neg : forall n, 1 <= n <= 5 ->
  Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (- n)))) = Z_to_bv 64 n.
Proof.
  intros n Hn. assert (H : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5) by lia.
  destruct H as [-> | [-> | [-> | [-> | ->]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma wu_lxn : forall n, 1 <= n <= 5 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (- n))) 18446744073709551615) = Z_to_bv 64 (n - 1).
Proof.
  intros n Hn. assert (H : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5) by lia.
  destruct H as [-> | [-> | [-> | [-> | ->]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma wu_bytes_snoc : forall m A k P b, k = Z.of_nat (length P) -> bytes_at rsegs m A P -> A + k + 1 <= 2 ^ 64 ->
  bytes_at rsegs (write_to_mem m (wa (A + k)) [b]) A (P ++ [b]).
Proof.
  intros m A k P b Hk HP HA. pose proof (bytes_at_bound rsegs m A P HP) as HB.
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HP | lia | cbn [length]; lia | cbn [length]; lia].
  - rewrite <- Hk. apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma wu_stk_wr : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. apply (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma wu_turn : forall (x i B : Z) (ra sq gp tp t2 s0 s1 a0 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
  0 <= x < 65536 -> 0 <= i < 5 -> 0 <= B -> B + 16 <= 2 ^ 64 ->
  store_ok rsegs m (wa (B + 11 + i)) 1 = true ->
  (forall y1 y2 y3 : word, 9 < x ->
     evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 9) (Z_to_bv 64 (i + 1)) y1 s0 s1 a0 (Z_to_bv 64 (x / 10))
                         (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (- (i + 1))) (Z_to_bv 64 5) (Z_to_bv 64 10)
                         (Z_to_bv 64 (B + 11)) (Z_to_bv 64 3435986944) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y2 y3 t5 t6)
                  F (Z_to_bv 64 0x14e80) fc None (write_to_mem m (wa (B + 11 + i)) [write_uint_dg (x mod 10)])
                  (seg_rom rsegs))) ->
  (forall y1 y2 y3 : word, x <= 9 ->
     evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 9) (Z_to_bv 64 (i + 1)) y1 s0 s1 a0 (Z_to_bv 64 (x / 10))
                         (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (- (i + 1))) (Z_to_bv 64 5) (Z_to_bv 64 10)
                         (Z_to_bv 64 (B + 11)) (Z_to_bv 64 3435986944) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y2 y3 t5 t6)
                  F (Z_to_bv 64 0x14ebc) fc None (write_to_mem m (wa (B + 11 + i)) [write_uint_dg (x mod 10)])
                  (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 9) (Z_to_bv 64 i) t2 s0 s1 a0 (Z_to_bv 64 x) a2 (Z_to_bv 64 (- i))
                      (Z_to_bv 64 5) (Z_to_bv 64 10) (Z_to_bv 64 (B + 11)) (Z_to_bv 64 3435986944)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14e80) fc None m (seg_rom rsegs)).
Proof.
  intros x i B ra sq gp tp t2 s0 s1 a0 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q Hx Hi HB HB2 HS KS KE.
  step. br false.
  do 13 step.
  step.
  rewrite (wu_q x) by lia. rewrite (wu_dig x) by lia. rewrite (wu_t1 x) by lia. rewrite (wu_dec i) by lia.
  destruct (Z.ltb_spec 9 x) as [HC | HC].
  - br true. apply (KS _ _ _ HC).
  - br false. apply (KE _ _ _ HC).
Qed.

Lemma wu_loop1 : forall (k : nat) (x i B o N lo : Z) (P : list byte)
  (ra sq gp tp t2 s0 s1 a0 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w3 w6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (Q : machine_state -> Prop),
  0 <= x < 10 ^ Z.of_nat (S k) -> x < 65536 -> i = Z.of_nat (length P) -> i + Z.of_nat (S k) <= 5 ->
  lo <= B -> B + 16 <= 2 ^ 64 ->
  w3 = Z_to_bv 64 (- i) -> w6 = Z_to_bv 64 (B + 11) ->
  stk rsegs m lo (B + 16) -> bytes_at rsegs m (B + 11) P ->
  munch [(B, B + 16); (o, o + N)] m0 m -> wmono rsegs m0 m ->
  (forall (m' : word -> option byte) (y1 y2 y3 y4 y5 y6 y7 : word),
     y4 = Z_to_bv 64 (i + Z.of_nat (length (write_uint_lsd (S k) x))) ->
     y5 = Z_to_bv 64 (- (i + Z.of_nat (length (write_uint_lsd (S k) x)))) ->
     stk rsegs m' lo (B + 16) -> bytes_at rsegs m' (B + 11) (P ++ write_uint_lsd (S k) x) ->
     munch [(B, B + 16); (o, o + N)] m0 m' -> wmono rsegs m0 m' ->
     evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 9) y1 y2 s0 s1 a0 y3 y4 y5 (Z_to_bv 64 5) (Z_to_bv 64 10) w6
                         (Z_to_bv 64 3435986944) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y6 y7 t5 t6)
                  F (Z_to_bv 64 0x14ebc) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 9) (Z_to_bv 64 i) t2 s0 s1 a0 (Z_to_bv 64 x) a2 w3
                      (Z_to_bv 64 5) (Z_to_bv 64 10) w6 (Z_to_bv 64 3435986944)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14e80) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros x i B o N lo P ra sq gp tp t2 s0 s1 a0 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w3 w6 F fc m0 m Q
      Hx Hx' HP Hi HL HB E3 E6 ST BP MU WM K;
    subst w3 w6; pose proof ST as (Hlo & _ & _);
    (assert (HS : store_ok rsegs m (wa (B + 11 + i)) 1 = true)
      by (apply (wr_at_store_ok rsegs m (B + 11) 5 i 1);
          [eapply wu_stk_wr; [exact ST | lia | lia | lia] | lia | cbn; lia])).
  - cbn in Hx.
    eapply wu_turn; [lia | lia | lia | lia | exact HS | | ].
    + intros y1 y2 y3 HC. exfalso. lia.
    + intros y1 y2 y3 HC. eapply K.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * apply stk_write; [exact ST | lia | cbn [length]; lia].
      * rewrite wu_lsd_lt10 by lia. apply wu_bytes_snoc; [exact HP | exact BP | lia].
      * apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
      * apply wmono_write. exact WM.
  - eapply wu_turn; [lia | lia | lia | lia | exact HS | | ].
    + intros y1 y2 y3 HC.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
      eapply (IH (x / 10) (i + 1) B o N lo (P ++ [write_uint_dg (x mod 10)])) with (m0 := m0).
      * split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
      * apply Z.div_lt_upper_bound; lia.
      * rewrite length_app. cbn [length]. lia.
      * lia.
      * exact HL.
      * exact HB.
      * reflexivity.
      * reflexivity.
      * apply stk_write; [exact ST | lia | cbn [length]; lia].
      * apply wu_bytes_snoc; [exact HP | exact BP | lia].
      * apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
      * apply wmono_write. exact WM.
      * intros m' z1 z2 z3 z4 z5 z6 z7 E4 E5 ST' BP' MU' WM'.
        rewrite wu_lsd_ge10 in K by lia. cbn [length] in K.
        apply K; [ rewrite E4; f_equal; lia | rewrite E5; f_equal; lia
                 | exact ST' | rewrite <- app_assoc in BP'; exact BP' | exact MU' | exact WM' ].
    + intros y1 y2 y3 HC. eapply K.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * apply stk_write; [exact ST | lia | cbn [length]; lia].
      * rewrite wu_lsd_lt10 by lia. apply wu_bytes_snoc; [exact HP | exact BP | lia].
      * apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
      * apply wmono_write. exact WM.
Qed.

Lemma wu_loop2 : forall (post pre : list byte) (o N B lo : Z)
  (ra sq gp tp t0 t1 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w0 w2 w3 w4 w5 w7 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (Q : machine_state -> Prop),
  post <> [] -> N = Z.of_nat (length pre + length post) -> N <= 5 ->
  lo <= B -> B + 16 <= 2 ^ 64 -> 0 <= o -> o + N <= 2 ^ 64 -> (o + N <= B \/ B + 16 <= o) ->
  w0 = Z_to_bv 64 (o + Z.of_nat (length pre)) ->
  w2 = Z_to_bv 64 N ->
  w3 = Z_to_bv 64 (Z.of_nat (length post) - 1) ->
  w4 = Z_to_bv 64 (Z.of_nat (length pre)) ->
  w5 = Z_to_bv 64 (2 ^ 64 - 1 - o) ->
  w7 = Z_to_bv 64 (B + 11) ->
  stk rsegs m lo (B + 16) -> wr_at rsegs m o N ->
  bytes_at rsegs m (B + 11) (rev (pre ++ post)) -> bytes_at rsegs m o pre ->
  munch [(B, B + 16); (o, o + N)] m0 m -> wmono rsegs m0 m ->
  (forall (m' : word -> option byte) (y0 y1 y2 y3 : word),
     stk rsegs m' lo (B + 16) -> bytes_at rsegs m' o (pre ++ post) ->
     munch [(B, B + 16); (o, o + N)] m0 m' -> wmono rsegs m0 m' ->
     evt rsegs Q (MS (mkR ra sq gp tp y0 t1 t2 s0 s1 y1 a1 w2 y2 y3 w5 (Z_to_bv 64 4) w7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14ef8) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp t0 t1 t2 s0 s1 w0 a1 w2 w3 w4 w5 (Z_to_bv 64 4) w7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14ed4) fc None m (seg_rom rsegs)).
Proof.
  induction post as [|b post IH];
    intros pre o N B lo ra sq gp tp t0 t1 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w0 w2 w3 w4 w5 w7
      F fc m0 m Q Hne HN HN5 HL HB Ho HoN HD E0 E2 E3 E4 E5 E7 ST HW BT BP MU WM K; [congruence|].
  replace (Z.of_nat (length (b :: post)) - 1) with (Z.of_nat (length post)) in E3 by (cbn [length]; lia).
  cbn [length] in HN.
  subst w0 w2 w3 w4 w5 w7. pose proof ST as (Hlo & _ & _).
  assert (RD : ov_read_bytes rsegs m (wa (B + 11 + Z.of_nat (length post))) 1 = Some [b]).
  { rewrite (bytes_at_read rsegs m (B + 11) _ (Z.of_nat (length post)) 1 BT)
      by (rewrite ?length_rev, ?length_app; cbn [length]; lia).
    f_equal. apply wu_nth_rev. }
  assert (HS : store_ok rsegs m (wa (o + Z.of_nat (length pre))) 1 = true).
  { apply (wr_at_store_ok rsegs m o N); [exact HW | lia | lia]. }
  step. br false.
  step. br false.
  do 6 step.
  step.
  rewrite le1_zxb.
  destruct post as [|b' post']; cbn [length] in HN.
  - br false.
    eapply K.
    + apply stk_write; [exact ST | lia | cbn [length]; lia].
    + apply wu_bytes_snoc; [reflexivity | exact BP | lia].
    + apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
    + apply wmono_write. exact WM.
  - br true.
    eapply (IH (pre ++ [b]) o N B lo) with (m0 := m0).
    + discriminate.
    + rewrite length_app. cbn [length] in *. lia.
    + exact HN5.
    + exact HL.
    + exact HB.
    + exact Ho.
    + exact HoN.
    + exact HD.
    + rewrite length_app. cbn [length]. f_equal; lia.
    + reflexivity.
    + rewrite unsigned_lit by (cbn [length] in *; lia).
      rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); cbn [length] in *; lia).
      f_equal; lia.
    + rewrite length_app. cbn [length]. f_equal; lia.
    + reflexivity.
    + reflexivity.
    + apply stk_write; [exact ST | lia | cbn [length]; lia].
    + apply wr_at_write. exact HW.
    + apply bytes_at_write_other;
        [rewrite <- app_assoc; exact BT | lia | cbn [length]; lia
        | rewrite length_rev, !length_app; cbn [length] in *; lia].
    + apply wu_bytes_snoc; [reflexivity | exact BP | lia].
    + apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
    + apply wmono_write. exact WM.
    + intros m' y0 y1 y2 y3 ST' BP' MU' WM'.
      apply (K m' y0 y1 y2 y3); [exact ST' | rewrite <- app_assoc in BP'; exact BP' | exact MU' | exact WM'].
Qed.

Theorem write_uint_holds : write_uint_contract.
Proof.
  unfold write_uint_contract, WRITE_UINT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o v lo
    E0 E1 Hv HW ST HLO HD.
  subst a0 a1.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & Hhi & _).
  pose proof HW as (Ho & HoN & _).
  pose proof (wu_lsd5 v) as HL5.
  pose proof (wu_n_eq v) as HNE.
  replace (bv_unsigned sp) with (bv_unsigned sp + -16 + 16) in ST by lia.
  do 9 step.
  eapply (wu_loop1 4 v 0 (bv_unsigned sp + -16) o (write_uint_n v) lo []) with (m0 := m).
  - cbn. lia.
  - lia.
  - reflexivity.
  - cbn. lia.
  - lia.
  - lia.
  - reflexivity.
  - f_equal; lia.
  - exact ST.
  - apply bytes_at_nil. lia.
  - apply munch_refl.
  - apply wmono_refl.
  - intros m1 y1 y2 y3 y4 y5 y6 y7 E4 E5 ST1 BT1 MU1 WM1.
    assert (E4' : y4 = Z_to_bv 64 (write_uint_n v)) by (rewrite E4, HNE; f_equal; lia).
    assert (E5' : y5 = Z_to_bv 64 (- write_uint_n v)) by (rewrite E5, HNE; f_equal; lia).
    clear E4 E5. subst y4 y5.
    do 6 step.
    rewrite (wu_neg (write_uint_n v)) by lia.
    eapply (wu_loop2 (write_uint_D v) [] o (write_uint_n v) (bv_unsigned sp + -16) lo) with (m0 := m).
    + intros E. apply (f_equal (@length byte)) in E. unfold write_uint_D in E. rewrite length_rev in E.
      cbn [length] in E. lia.
    + reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + f_equal; cbn [length]; lia.
    + reflexivity.
    + rewrite (wu_lxn (write_uint_n v)) by lia. reflexivity.
    + reflexivity.
    + rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. f_equal; lia.
    + f_equal; lia.
    + exact ST1.
    + eapply wr_at_transport; [exact HW | exact WM1].
    + cbn [app]. unfold write_uint_D. rewrite rev_involutive. exact BT1.
    + apply bytes_at_nil. lia.
    + exact MU1.
    + exact WM1.
    + intros m2 z0 z1 z2 z3 ST2 BT2 MU2 WM2.
      step. step. step.
      apply evt_done. cbv beta. do 13 eexists. split; [reflexivity|].
      split.
      { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside].
        intros x [H1 [H2 _]]. repeat split; lia. }
      split; [exact WM2|].
      split.
      { replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in ST2 by lia. exact ST2. }
      exact BT2.
Qed.
