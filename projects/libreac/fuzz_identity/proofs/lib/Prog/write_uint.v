From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import write_uint_c.
Import ListNotations.
Open Scope Z_scope.

Lemma wu_q : forall x, 0 <= x < 65536 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64
    (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48)) * 3435986944) 64))) 19) = Z_to_bv 64 (x / 10).
Proof.
  intros x Hx. f_equal.
  rewrite (unsigned_lit x) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 48) with 281474976710656. change (2 ^ 64) with 18446744073709551616. change (2 ^ 19) with 524288.
  rewrite (unsigned_lit (x * 281474976710656)) by lia.
  replace (x * 281474976710656 * 3435986944) with (x * 52429 * 18446744073709551616) by lia.
  rewrite Z.div_mul by lia.
  rewrite (unsigned_lit (x * 52429)) by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma wu_t1 : forall x, 0 <= x < 65536 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48))) 48 = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 48) with 281474976710656.
  rewrite (unsigned_lit (x * 281474976710656)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 48) with 281474976710656.
  apply Z.div_mul. lia.
Qed.

Lemma wu_sh32 : forall z, 0 <= z < 2 ^ 32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 32))) 32 = z.
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296 in *.
  rewrite (unsigned_lit (z * 4294967296)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
  apply Z.div_mul. lia.
Qed.

Lemma wu_not : forall z e, 0 <= z < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 z)) 18446744073709551615 + e) = Z_to_bv 64 (e - z - 1).
Proof.
  intros z e Hz. rewrite (unsigned_lit z) by lia. rewrite zb_lxor_ones by lia.
  apply Z_to_bv_eqm. replace (18446744073709551615 - z + e) with (e - z - 1 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma wu_cnt : forall i, 0 <= i < 5 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + 1)) = Z_to_bv 64 (i + 1).
Proof.
  intros i Hi. rewrite (unsigned_lit i) by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Lemma wu_lor48 : forall r, 0 <= r < 10 -> Z.lor r 48 = 48 + r.
Proof.
  intros r Hr.
  assert (H : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.

Lemma wu_dig : forall x, 0 <= x < 65536 ->
  le1 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) -
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (x / 10)) * 10)))))) 48))
  = [write_uint_dg (x mod 10)].
Proof.
  intros x Hx.
  assert (Hq : 0 <= x / 10 <= 6553) by (Z.div_mod_to_equations; lia).
  assert (Hr : 0 <= x mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  rewrite (unsigned_lit x), (unsigned_lit (x / 10)) by lia.
  rewrite (unsigned_lit (x / 10 * 10)) by lia.
  replace (x - x / 10 * 10) with (x mod 10) by (rewrite Z.mod_eq by lia; lia).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; lia).
  rewrite (unsigned_lit (x mod 10)) by lia.
  rewrite wu_lor48 by lia.
  unfold le1. rewrite (unsigned_lit (48 + x mod 10)) by lia.
  reflexivity.
Qed.

Lemma wu_eqb : forall X Y, 0 <= X < 2 ^ 64 -> 0 <= Y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 X) (Z_to_bv 64 Y) = (X =? Y).
Proof. intros X Y HX HY. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma wu_ltu : forall X Y, 0 <= X < 2 ^ 64 -> 0 <= Y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 X) (Z_to_bv 64 Y) = (X <? Y).
Proof. intros X Y HX HY. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma wu_lsd_lt10 : forall k x, x < 10 -> write_uint_lsd (S k) x = [write_uint_dg (x mod 10)].
Proof. intros k x Hx. cbn [write_uint_lsd]. rewrite (proj2 (Z.ltb_lt x 10) Hx). reflexivity. Qed.

Lemma wu_lsd_ge10 : forall k x, 10 <= x ->
  write_uint_lsd (S k) x = write_uint_dg (x mod 10) :: write_uint_lsd k (x / 10).
Proof. intros k x Hx. cbn [write_uint_lsd]. rewrite (proj2 (Z.ltb_ge x 10) Hx). reflexivity. Qed.

Lemma wu_lsd_len : forall k x, (length (write_uint_lsd k x) <= k)%nat.
Proof.
  induction k as [|k IH]; intros x; cbn [write_uint_lsd length]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|]. specialize (IH (x / 10)). lia.
Qed.

Lemma wu_lsd5 : forall v, 1 <= Z.of_nat (length (write_uint_lsd 5 v)) <= 5.
Proof.
  intros v. pose proof (wu_lsd_len 5 v) as H.
  assert (H1 : (1 <= length (write_uint_lsd 5 v))%nat) by (cbn [write_uint_lsd length]; lia).
  lia.
Qed.

Lemma wu_n_eq : forall v, write_uint_n v = Z.of_nat (length (write_uint_lsd 5 v)).
Proof. intros v. unfold write_uint_n, write_uint_D. rewrite length_rev. reflexivity. Qed.

Lemma wu_nth_rev : forall (pre post : list byte) (b : byte),
  firstn 1 (skipn (Z.to_nat (Z.of_nat (length post))) (rev (pre ++ b :: post))) = [b].
Proof.
  intros pre post b. rewrite Nat2Z.id, rev_app_distr. cbn [rev]. rewrite <- app_assoc.
  rewrite skipn_app, skipn_all2 by (rewrite length_rev; lia).
  rewrite length_rev, Nat.sub_diag. reflexivity.
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

Lemma wu_turn : forall (x i B : Z) (ra sq gp tp t1 t2 s0 s1 a2 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
  0 <= x < 65536 -> 0 <= i < 5 -> 0 <= B -> B + 16 <= 2 ^ 64 ->
  store_ok rsegs m (wa (B + 11 + i)) 1 = true ->
  (forall y : word, 9 < x ->
     evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 (i + 1)) y (Z_to_bv 64 (x / 10)) s0 s1 (Z_to_bv 64 (i + 1))
                         (Z_to_bv 64 (x / 10)) a2 (Z_to_bv 64 10) (Z_to_bv 64 (B + 11)) (Z_to_bv 64 3435986944)
                         (Z_to_bv 64 i) (Z_to_bv 64 9) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (B + 11 + i)) t4 t5 t6)
                  F (Z_to_bv 64 0x14968) fc None (write_to_mem m (wa (B + 11 + i)) [write_uint_dg (x mod 10)])
                  (seg_rom rsegs))) ->
  (forall y : word, x <= 9 ->
     evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 (i + 1)) y (Z_to_bv 64 (x / 10)) s0 s1 (Z_to_bv 64 (i + 1))
                         (Z_to_bv 64 (x / 10)) a2 (Z_to_bv 64 10) (Z_to_bv 64 (B + 11)) (Z_to_bv 64 3435986944)
                         (Z_to_bv 64 i) (Z_to_bv 64 9) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (B + 11 + i)) t4 t5 t6)
                  F (Z_to_bv 64 0x149a0) fc None (write_to_mem m (wa (B + 11 + i)) [write_uint_dg (x mod 10)])
                  (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 i) t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 x) a2
                      (Z_to_bv 64 10) (Z_to_bv 64 (B + 11)) (Z_to_bv 64 3435986944) a6 (Z_to_bv 64 9)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14968) fc None m (seg_rom rsegs)).
Proof.
  intros x i B ra sq gp tp t1 t2 s0 s1 a2 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q Hx Hi HB HB2 HS KS KE.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  rewrite (wu_q x) by lia. rewrite (wu_dig x) by lia. rewrite (wu_cnt i) by lia. rewrite (wu_t1 x) by lia.
  rewrite (wu_ltu 9 x) by lia.
  destruct (Z.ltb_spec 9 x) as [HC | HC].
  - apply (KS (Z_to_bv 64 x) HC).
  - apply (KE (Z_to_bv 64 x) HC).
Qed.

Lemma wu_loop1 : forall (k : nat) (x i B o N lo : Z) (P : list byte)
  (ra sq gp tp t1 t2 s0 s1 a2 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w4 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (Q : machine_state -> Prop),
  0 <= x < 10 ^ Z.of_nat (S k) -> x < 65536 -> i = Z.of_nat (length P) -> i + Z.of_nat (S k) <= 5 ->
  lo <= B -> B + 16 <= 2 ^ 64 ->
  w4 = Z_to_bv 64 (B + 11) ->
  stk rsegs m lo (B + 16) -> bytes_at rsegs m (B + 11) P ->
  munch [(B, B + 16); (o, o + N)] m0 m -> wmono rsegs m0 m ->
  (forall (m' : word -> option byte) (y1 y2 y3 y4 yt0 ya0 ya6 : word),
     yt0 = Z_to_bv 64 (i + Z.of_nat (length (write_uint_lsd (S k) x))) ->
     ya0 = Z_to_bv 64 (i + Z.of_nat (length (write_uint_lsd (S k) x))) ->
     ya6 = Z_to_bv 64 (i + Z.of_nat (length (write_uint_lsd (S k) x)) - 1) ->
     stk rsegs m' lo (B + 16) -> bytes_at rsegs m' (B + 11) (P ++ write_uint_lsd (S k) x) ->
     munch [(B, B + 16); (o, o + N)] m0 m' -> wmono rsegs m0 m' ->
     evt rsegs Q (MS (mkR ra sq gp tp yt0 y1 y2 s0 s1 ya0 y3 a2 (Z_to_bv 64 10) w4 (Z_to_bv 64 3435986944) ya6
                         (Z_to_bv 64 9) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y4 t4 t5 t6)
                  F (Z_to_bv 64 0x149a0) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp (Z_to_bv 64 i) t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 x) a2 (Z_to_bv 64 10) w4
                      (Z_to_bv 64 3435986944) a6 (Z_to_bv 64 9) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14968) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros x i B o N lo P ra sq gp tp t1 t2 s0 s1 a2 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w4 F fc m0 m Q
      Hx Hx' HP Hi HL HB E4 ST BP MU WM K;
    subst w4; pose proof ST as (Hlo & _ & _);
    (assert (HS : store_ok rsegs m (wa (B + 11 + i)) 1 = true)
      by (apply (wr_at_store_ok rsegs m (B + 11) 5 i 1);
          [eapply wu_stk_wr; [exact ST | lia | lia | lia] | lia | cbn; lia])).
  - cbn in Hx.
    eapply wu_turn; [lia | lia | lia | lia | exact HS | | ].
    + intros y HC. exfalso. lia.
    + intros y HC. eapply K.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * apply stk_write; [exact ST | lia | cbn [length]; lia].
      * rewrite wu_lsd_lt10 by lia. apply wu_bytes_snoc; [exact HP | exact BP | lia].
      * apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
      * apply wmono_write. exact WM.
  - eapply wu_turn; [lia | lia | lia | lia | exact HS | | ].
    + intros y HC.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
      eapply (IH (x / 10) (i + 1) B o N lo (P ++ [write_uint_dg (x mod 10)])) with (m0 := m0).
      * split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
      * apply Z.div_lt_upper_bound; lia.
      * rewrite length_app. cbn [length]. lia.
      * lia.
      * exact HL.
      * exact HB.
      * reflexivity.
      * apply stk_write; [exact ST | lia | cbn [length]; lia].
      * apply wu_bytes_snoc; [exact HP | exact BP | lia].
      * apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
      * apply wmono_write. exact WM.
      * intros m' y1 y2 y3 y4 yt0 ya0 ya6 Et0 Ea0 Ea6 ST' BP' MU' WM'.
        rewrite wu_lsd_ge10 in K by lia. cbn [length] in K.
        apply K; [ rewrite Et0; f_equal; lia | rewrite Ea0; f_equal; lia | rewrite Ea6; f_equal; lia
                 | exact ST' | rewrite <- app_assoc in BP'; exact BP' | exact MU' | exact WM' ].
    + intros y HC. eapply K.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * rewrite wu_lsd_lt10 by lia. cbn [length]. f_equal; lia.
      * apply stk_write; [exact ST | lia | cbn [length]; lia].
      * rewrite wu_lsd_lt10 by lia. apply wu_bytes_snoc; [exact HP | exact BP | lia].
      * apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
      * apply wmono_write. exact WM.
Qed.

Lemma wu_loop2 : forall (post pre : list byte) (o N B lo : Z)
  (ra sq gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w1 w2 w3 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (Q : machine_state -> Prop),
  post <> [] -> N = Z.of_nat (length pre + length post) -> N <= 5 ->
  lo <= B -> B + 16 <= 2 ^ 64 -> 0 <= o -> o + N <= 2 ^ 64 -> (o + N <= B \/ B + 16 <= o) ->
  w1 = Z_to_bv 64 (B + 10 + Z.of_nat (length post)) ->
  w2 = Z_to_bv 64 (o + Z.of_nat (length pre)) ->
  w3 = Z_to_bv 64 (B + 10) ->
  stk rsegs m lo (B + 16) -> wr_at rsegs m o N ->
  bytes_at rsegs m (B + 11) (rev (pre ++ post)) -> bytes_at rsegs m o pre ->
  munch [(B, B + 16); (o, o + N)] m0 m -> wmono rsegs m0 m ->
  (forall (m' : word -> option byte) (y1 y2 y4 : word),
     stk rsegs m' lo (B + 16) -> bytes_at rsegs m' o (pre ++ post) ->
     munch [(B, B + 16); (o, o + N)] m0 m' -> wmono rsegs m0 m' ->
     evt rsegs Q (MS (mkR ra sq gp tp t0 t1 t2 s0 s1 a0 y1 y2 w3 y4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x149cc) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sq gp tp t0 t1 t2 s0 s1 a0 w1 w2 w3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x149b8) fc None m (seg_rom rsegs)).
Proof.
  induction post as [|b post IH];
    intros pre o N B lo ra sq gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w1 w2 w3
      F fc m0 m Q Hne HN HN5 HL HB Ho HoN HD E1 E2 E3 ST HW BT BP MU WM K; [congruence|].
  subst w1 w2. pose proof ST as (Hlo & _ & _).
  assert (RD : ov_read_bytes rsegs m (wa (B + 10 + Z.of_nat (length (b :: post)))) 1 = Some [b]).
  { replace (B + 10 + Z.of_nat (length (b :: post))) with (B + 11 + Z.of_nat (length post)) by (cbn [length]; lia).
    rewrite (bytes_at_read rsegs m (B + 11) _ (Z.of_nat (length post)) 1 BT)
      by (rewrite ?length_rev, ?length_app; cbn [length]; lia).
    f_equal. apply wu_nth_rev. }
  assert (HS : store_ok rsegs m (wa (o + Z.of_nat (length pre))) 1 = true).
  { apply (wr_at_store_ok rsegs m o N); [exact HW | lia | cbn [length] in HN; lia]. }
  subst w3.
  step. step. step. step. step.
  rewrite le1_zxb.
  lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?X) (Z_to_bv 64 ?Y)] =>
    rewrite (wu_eqb X Y) by (cbn [length] in *; lia) end.
  destruct post as [|b' post'].
  - rewrite (proj2 (Z.eqb_eq _ _)) by (cbn [length]; lia). cbn [negb].
    eapply K.
    + apply stk_write; [exact ST | lia | cbn [length] in *; lia].
    + apply wu_bytes_snoc; [reflexivity | exact BP | cbn [length] in HN; lia].
    + apply munch_write; [exact MU | lia | cbn [length] in *; lia | cbn [inside length] in *; lia].
    + apply wmono_write. exact WM.
  - rewrite (proj2 (Z.eqb_neq _ _)) by (cbn [length]; lia). cbn [negb].
    eapply (IH (pre ++ [b]) o N B lo) with (m0 := m0).
    + discriminate.
    + rewrite length_app. cbn [length] in *. lia.
    + exact HN5.
    + exact HL.
    + exact HB.
    + exact Ho.
    + exact HoN.
    + exact HD.
    + f_equal; cbn [length]; lia.
    + f_equal; rewrite length_app; cbn [length]; lia.
    + reflexivity.
    + apply stk_write; [exact ST | lia | cbn [length] in *; lia].
    + apply wr_at_write. exact HW.
    + apply bytes_at_write_other;
        [rewrite <- app_assoc; exact BT | lia | cbn [length] in *; lia
        | rewrite length_rev, !length_app; cbn [length] in *; lia].
    + apply wu_bytes_snoc; [reflexivity | exact BP | cbn [length] in HN; lia].
    + apply munch_write; [exact MU | lia | cbn [length] in *; lia | cbn [inside length] in *; lia].
    + apply wmono_write. exact WM.
    + intros m' y1 y2 y4 ST' BP' MU' WM'.
      apply K; [exact ST' | rewrite <- app_assoc in BP'; exact BP' | exact MU' | exact WM'].
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
  step. step. step. step. step. step. step. step. step.
  eapply (wu_loop1 4 v 0 (bv_unsigned sp + -16) o (write_uint_n v) lo []) with (m0 := m).
  - cbn. lia.
  - lia.
  - reflexivity.
  - cbn. lia.
  - lia.
  - lia.
  - f_equal; lia.
  - exact ST.
  - apply bytes_at_nil. lia.
  - apply munch_refl.
  - apply wmono_refl.
  - intros m1 y1 y2 y3 y4 yt0 ya0 ya6 Et0 Ea0 Ea6 ST1 BT1 MU1 WM1.
    assert (Ea0' : ya0 = Z_to_bv 64 (write_uint_n v)) by (rewrite Ea0, HNE; f_equal; lia).
    clear Ea0. subst yt0 ya0 ya6.
    step. step. step. step. step. step.
    eapply (wu_loop2 (write_uint_D v) [] o (write_uint_n v) (bv_unsigned sp + -16) lo) with (m0 := m).
    + intros E. apply (f_equal (@length byte)) in E. unfold write_uint_D in E. rewrite length_rev in E.
      cbn [length] in E. lia.
    + rewrite HNE. unfold write_uint_D. rewrite length_rev. cbn [length]. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite wu_sh32 by lia. f_equal; unfold write_uint_D; rewrite length_rev; lia.
    + f_equal; cbn [length]; lia.
    + rewrite wu_sh32 by lia. rewrite wu_not by lia. f_equal; lia.
    + exact ST1.
    + eapply wr_at_transport; [exact HW | exact WM1].
    + cbn [app]. unfold write_uint_D. rewrite rev_involutive. exact BT1.
    + apply bytes_at_nil. lia.
    + exact MU1.
    + exact WM1.
    + intros m2 z1 z2 z4 ST2 BT2 MU2 WM2.
      step. step.
      apply evt_done. cbv beta. do 12 eexists. split; [reflexivity|].
      split.
      { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside].
        intros x [H1 [H2 _]]. repeat split; lia. }
      split; [exact WM2|].
      split.
      { replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in ST2 by lia. exact ST2. }
      exact BT2.
Qed.
