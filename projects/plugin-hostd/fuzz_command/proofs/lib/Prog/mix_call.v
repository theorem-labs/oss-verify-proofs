From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strlen_c mix_call_c.
Import ListNotations.
Open Scope Z_scope.

Lemma byte_mod64 : forall b : byte, bv_unsigned b mod 2^64 = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  apply Z.mod_small. lia.
Qed.

Lemma bv_eqb_lits : forall x y, 1 <= x <= 2^64 -> 1 <= y <= 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616 in *.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_lit64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma skipn_len : forall {X} (l rest : list X) j r, skipn j l = r :: rest -> (j + S (length rest) = length l)%nat.
Proof.
  intros X l. induction l as [|y l IH]; intros rest j r H; destruct j; cbn in *; try discriminate.
  - inversion H; subst. reflexivity.
  - apply IH in H. lia.
Qed.

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

Lemma shl3 : forall k, (k <= 16)%nat ->
  Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat k))) 3 = 8 * Z.of_nat k.
Proof.
  intros k Hk. rewrite (unsigned_lit (Z.of_nat k)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2^3) with 8. lia.
Qed.

Ltac fnv_tac HP :=
  try unfold zxb; repeat rewrite unsigned_lit_wrap; rewrite ?HP, ?byte_mod64;
  rewrite ?Z.mul_mod_idemp_l by lia; try reflexivity.

Section FnLoop.
Variables (r1 r2 r3 r4 r5 r6 r7 r9 r10 r11 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 e : word)
  (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte) (p : Z) (bs : list byte).
Hypothesis HB : bytes_at rsegs mc p bs.
Hypothesis He : e = Z_to_bv 64 (p + Z.of_nat (length bs)).
Hypothesis HP : bv_unsigned r18 = FNV_P.

Lemma fn_loop : forall rest j (w q r14 r15 : word) (P : machine_state -> Prop),
  skipn j bs = rest -> rest <> [] -> bv_unsigned q = p + Z.of_nat j ->
  (forall w' q' x14 x15 : word, bv_unsigned w' = fnv (bv_unsigned w) rest ->
     evt rsegs P (MS (mkR r1 r2 r3 r4 r5 r6 r7 w' r9 r10 r11 e q' x14 x15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                          r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15d30) fc None mc (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR r1 r2 r3 r4 r5 r6 r7 w r9 r10 r11 e q r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                       r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15d18) fc None mc (seg_rom rsegs)).
Proof.
  induction rest as [|b rest IH]; intros j w q r14 r15 P Hs Hne Hq K; [congruence|].
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  pose proof (skipn_len _ _ _ _ Hs) as Hj.
  assert (Eq : q = Z_to_bv 64 (p + Z.of_nat j)) by (apply bv_eq; rewrite unsigned_lit by lia; exact Hq).
  subst q.
  assert (RD : ov_read_bytes rsegs mc (wa (p + Z.of_nat j + 0)) 1 = Some [b]).
  { rewrite <- Z.add_assoc. rewrite (bytes_at_read rsegs mc p bs (Z.of_nat j + 0) 1 HB) by lia.
    rewrite Z.add_0_r, Nat2Z.id, Hs. reflexivity. }
  subst e.
  do 6 step.
  rewrite bv_eqb_lits by lia.
  destruct (Z.eqb_spec (p + Z.of_nat j + 1) (p + Z.of_nat (length bs))) as [E|E]; cbn [negb].
  - assert (rest = []) by (destruct rest; [reflexivity | cbn [length] in Hj; lia]). subst rest.
    eapply K. cbn [fnv]. fnv_tac HP.
  - eapply IH.
    + eapply skipn_succ_cons. exact Hs.
    + destruct rest; [cbn [length] in Hj; lia | discriminate].
    + rewrite unsigned_lit by lia. lia.
    + intros w' q' x14 x15 Hw'. apply K. rewrite Hw'. cbn [fnv]. f_equal. fnv_tac HP.
Qed.
End FnLoop.

Section ByteLoop.
Variables (r1 r2 r3 r4 r5 r6 r7 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 e : word)
  (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte) (p : Z) (bs : list byte).
Hypothesis HB : bytes_at rsegs mc p bs.
Hypothesis He : e = Z_to_bv 64 (p + Z.of_nat (length bs)).
Hypothesis HP : bv_unsigned r18 = FNV_P.

Lemma byte_loop : forall rest j (w q r11 r12 : word) (P : machine_state -> Prop),
  skipn j bs = rest -> rest <> [] -> bv_unsigned q = p + Z.of_nat j ->
  (forall w' q' x11 x12 : word, bv_unsigned w' = fnv (bv_unsigned w) rest ->
     evt rsegs P (MS (mkR r1 r2 r3 r4 r5 r6 r7 w' q' e x11 x12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                          r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15d88) fc None mc (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR r1 r2 r3 r4 r5 r6 r7 w q e r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                       r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15d70) fc None mc (seg_rom rsegs)).
Proof.
  induction rest as [|b rest IH]; intros j w q r11 r12 P Hs Hne Hq K; [congruence|].
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  pose proof (skipn_len _ _ _ _ Hs) as Hj.
  assert (Eq : q = Z_to_bv 64 (p + Z.of_nat j)) by (apply bv_eq; rewrite unsigned_lit by lia; exact Hq).
  subst q.
  assert (RD : ov_read_bytes rsegs mc (wa (p + Z.of_nat j + 0)) 1 = Some [b]).
  { rewrite <- Z.add_assoc. rewrite (bytes_at_read rsegs mc p bs (Z.of_nat j + 0) 1 HB) by lia.
    rewrite Z.add_0_r, Nat2Z.id, Hs. reflexivity. }
  subst e.
  do 6 step.
  rewrite bv_eqb_lits by lia.
  destruct (Z.eqb_spec (p + Z.of_nat j + 1) (p + Z.of_nat (length bs))) as [E|E]; cbn [negb].
  - assert (rest = []) by (destruct rest; [reflexivity | cbn [length] in Hj; lia]). subst rest.
    eapply K. cbn [fnv]. fnv_tac HP.
  - eapply IH.
    + eapply skipn_succ_cons. exact Hs.
    + destruct rest; [cbn [length] in Hj; lia | discriminate].
    + rewrite unsigned_lit by lia. lia.
    + intros w' q' x11 x12 Hw'. apply K. rewrite Hw'. cbn [fnv]. f_equal. fnv_tac HP.
Qed.
End ByteLoop.

Section ArgTail.
Variables (r1 r2 r3 r4 r5 r6 r7 r9 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte) (s : list byte).
Hypothesis HB : bytes_at rsegs mc (bv_unsigned r9) (s ++ [Z_to_bv 8 0]).
Hypothesis HL : Z.of_nat (length s) <= LMAX.
Hypothesis HP : bv_unsigned r18 = FNV_P.
Hypothesis H5 : bv_unsigned r21 = FNV_B0.
Hypothesis H7 : bv_unsigned r23 = 2^64 - 1.

Lemma arg_tail : forall (g : Z) (w a1 a2 : word) (P : machine_state -> Prop),
  bv_unsigned w = g ->
  (forall w' x9 x10 x11 x12 : word, bv_unsigned w' = mix g (s ++ [Z_to_bv 8 0]) ->
     evt rsegs P (MS (mkR r1 r2 r3 r4 r5 r6 r7 w' x9 x10 x11 x12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                          r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15d88) fc None mc (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR r1 r2 r3 r4 r5 r6 r7 w r9 (Z_to_bv 64 (Z.of_nat (length s))) a1 a2 r13 r14 r15 r16 r17 r18 r19
                       r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15d5c) fc None mc (seg_rom rsegs)).
Proof.
  intros g w a1 a2 P Hw K.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  pose proof (zr_word r9) as R9. unfold inr64 in R9.
  unfold LMAX in HL.
  step.
  unfold bv_eqb. rewrite Hw. try rewrite (unsigned_lit 0) by lia.
  destruct (Z.eqb_spec g 0) as [G0|G0]; cbn [negb].
  - step. step.
    unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length s))), H7 by lia.
    replace (Z.of_nat (length s) =? 2^64 - 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    eapply byte_loop with (bs := s ++ [Z_to_bv 8 0]) (p := bv_unsigned r9) (j := 0%nat) (rest := s ++ [Z_to_bv 8 0]).
    + exact HB.
    + f_equal. rewrite length_app. cbn [length]. lia.
    + exact HP.
    + reflexivity.
    + destruct s; discriminate.
    + lia.
    + intros w' q' x11 x12 Hw'. apply K. rewrite Hw', H5. unfold mix. rewrite G0. reflexivity.
  - step.
    unfold bv_eqb. rewrite (unsigned_lit (Z.of_nat (length s))), H7 by lia.
    replace (Z.of_nat (length s) =? 2^64 - 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    eapply byte_loop with (bs := s ++ [Z_to_bv 8 0]) (p := bv_unsigned r9) (j := 0%nat) (rest := s ++ [Z_to_bv 8 0]).
    + exact HB.
    + f_equal. rewrite length_app. cbn [length]. lia.
    + exact HP.
    + reflexivity.
    + destruct s; discriminate.
    + lia.
    + intros w' q' x11 x12 Hw'. apply K. rewrite Hw', Hw. unfold mix.
      replace (g =? 0) with false by (symmetry; apply Z.eqb_neq; exact G0). reflexivity.
Qed.
End ArgTail.

Section Outer.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1w : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (lo h fn : Z) (args : list (word * list byte)).
Hypothesis STRLEN : strlen_contract.
Hypothesis LO : lo + 80 <= bv_unsigned sp.
Hypothesis LA : (length args <= 6)%nat.
Hypothesis DC : bv_unsigned a1w + 56 <= bv_unsigned sp + -80 \/ bv_unsigned sp <= bv_unsigned a1w.
Hypothesis HARG : forall k p, nth_error args k = Some p ->
  mc_arg m (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned a1w) k p.

Definition mix_post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (mixcall h fn (map snd args)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Lemma mix_exit : forall mc junk (w : word) rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c
    t3c t4c t5c t6c,
  rw_cells rsegs mc (bv_unsigned sp + -80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv rsegs mc -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -80) ->
  bv_unsigned w = mixcall h fn (map snd args) ->
  evt rsegs mix_post
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0c t1c t2c w s1c a0c a1c a2c a3c a4c a5c a6c a7c
             s2c s3c s4c s5c s6c s7c s8 s9 s10 s11 t3c t4c t5c t6c)
        F (Z_to_bv 64 0x15d90) fc None mc (seg_rom rsegs)).
Proof.
  intros mc junk w rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c t3c t4c t5c t6c
    FR MI MU WM ST Hw.
  rewrite <- (Z_to_bv_lit_self w), Hw.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 11 step.
  release_frame FR ST (bv_unsigned sp).
  step.
  finish.
Qed.

Lemma outer : forall rest k (w : word) mc junk rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s5c s7c
    t3c t4c t5c t6c,
  skipn k args = rest -> rest <> [] ->
  mixcall h fn (map snd args) = fold_left (fun g a => mix g (a ++ [Z_to_bv 8 0])) (map snd rest) (bv_unsigned w) ->
  bv_unsigned s2c = FNV_P -> bv_unsigned s5c = FNV_B0 -> bv_unsigned s7c = 2^64 - 1 ->
  rw_cells rsegs mc (bv_unsigned sp + -80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv rsegs mc -> munch [(bv_unsigned sp + -80, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -80) ->
  evt rsegs mix_post
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0c t1c t2c w s1c a0c a1c a2c a3c a4c a5c a6c a7c
             s2c (Z_to_bv 64 (Z.of_nat (length args))) (Z_to_bv 64 (Z.of_nat k)) s5c (Z_to_bv 64 (bv_unsigned a1w + 8))
             s7c s8 s9 s10 s11 t3c t4c t5c t6c)
        F (Z_to_bv 64 0x15d48) fc None mc (seg_rom rsegs)).
Proof.
  induction rest as [|p rest IH];
    intros k w mc junk rac t0c t1c t2c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c s5c s7c t3c t4c t5c t6c
      Hs Hne Hf H2 H5 H7 FR MI MU WM ST; [congruence|].
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a1w) as Ra1. unfold inr64 in Ra1.
  pose proof (skipn_nth _ _ _ _ Hs) as NA.
  pose proof (skipn_len _ _ _ _ Hs) as Hk.
  destruct (HARG k p NA) as (HS & NZ & LM & slack & HP & SL & AP).
  pose proof (bytes_at_bound _ _ _ _ HS) as BS. rewrite length_le8 in BS.
  pose proof (bytes_at_bound _ _ _ _ HP) as BP. rewrite length_app in BP. cbn [length] in BP.
  assert (HSc : bytes_at rsegs mc (bv_unsigned a1w + 8 + 8 * Z.of_nat k) (le8 (fst p))).
  { eapply bytes_at_transport; [exact HS | exact MU |]. cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I]. }
  assert (HPc : bytes_at rsegs mc (bv_unsigned (fst p)) (snd p ++ Z_to_bv 8 0 :: slack)).
  { eapply bytes_at_transport; [exact HP | exact MU |]. cbn [disjoint_from]. rewrite length_app. cbn [length].
    split; [lia | exact I]. }
  assert (RS : ov_read_bytes rsegs mc (wa (bv_unsigned a1w + 8 + 8 * Z.of_nat k + 0)) 8 = Some (le8 (fst p))).
  { rewrite (bytes_at_read rsegs mc _ _ 0 8 HSc) by (rewrite ?length_le8; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. f_equal; apply firstn_all2; rewrite ?length_le8; lia. }
  clear HS HP HSc.
  step. step.
  rewrite (shl3 k) by lia.
  step. step. step.
  eapply evt_cut.
  { eapply STRLEN with (str := snd p) (slack := slack); [exact HPc | exact NZ | exact SL | exact MI]. }
  post_call rsegs mc.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
  assert (HB1 : bytes_at rsegs m1 (bv_unsigned (fst p)) (snd p ++ [Z_to_bv 8 0])).
  { replace (snd p ++ Z_to_bv 8 0 :: slack) with ((snd p ++ [Z_to_bv 8 0]) ++ slack) in HPc
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in HPc. exact (proj1 HPc). }
  eapply (arg_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (snd p) HB1 LM H2 H5 H7
            (bv_unsigned w)); [reflexivity |].
  intros w' y9 y10 y11 y12 Hw'.
  step. step.
  rewrite eqb_lit64 by lia.
  destruct (Z.eqb_spec (Z.of_nat k + 1) (Z.of_nat (length args))) as [EK|EK]; cbn [negb].
  - assert (rest = []) by (destruct rest; [reflexivity | cbn [length] in Hk; lia]). subst rest.
    eapply mix_exit; try eassumption.
    rewrite Hf, Hw'. reflexivity.
  - replace (Z_to_bv 64 (Z.of_nat k + 1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
    eapply IH; try eassumption.
    + eapply skipn_succ_cons. exact Hs.
    + destruct rest; [cbn [length] in Hk; lia | discriminate].
    + rewrite Hf, Hw'. reflexivity.
Qed.

End Outer.

Theorem mix_call_holds : strlen_contract -> mix_call_contract.
Proof.
  intros STRLEN. unfold mix_call_contract, MIX_CALL, MIX_CALL_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fn args
    MI ST LO HFN LA HH DH HARG HB0 DB0.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a1) as Ra1. unfold inr64 in Ra1.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (bytes_at_bound _ _ _ _ HH) as BH. rewrite length_app, !length_le4 in BH.
  carve_frame 80%nat ST.
  do 14 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (RB0 : ov_read_bytes rsegs m1 (wa FNV_B0_ADDR) 8 = Some (le8 (Z_to_bv 64 FNV_B0))).
  { replace FNV_B0_ADDR with (FNV_B0_ADDR + 0) at 1 by lia.
    rewrite (bytes_at_read rsegs m1 FNV_B0_ADDR _ 0 8 HB0) by (rewrite ?length_le8; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. f_equal; apply firstn_all2; rewrite ?length_le8; lia. }
  assert (RH4 : ov_read_bytes rsegs m1 (wa (bv_unsigned a1 + 4)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length args))))).
  { rewrite (bytes_at_read rsegs m1 _ _ 4 4 HH) by (rewrite ?length_app, ?length_le4; lia).
    change (Z.to_nat 4) with 4%nat. rewrite skipn_app, skipn_all2 by (rewrite length_le4; lia).
    rewrite length_le4, Nat.sub_diag. cbn [app skipn]. f_equal; apply firstn_all2; rewrite ?length_le4; lia. }
  assert (HFL : bytes_at rsegs m1 (bv_unsigned a1) (le4 (Z_to_bv 64 fn))).
  { apply bytes_at_app in HH. exact (proj1 HH). }
  step.
  unfold bv_eqb. try rewrite (unsigned_lit 0) by lia.
  destruct (Z.eqb_spec (bv_unsigned a0) 0) as [A0|A0]; cbn [negb]; [step|].
  all: do 3 step.
  all: eapply fn_loop with (bs := le4 (Z_to_bv 64 fn)) (p := bv_unsigned a1) (j := 0%nat) (rest := le4 (Z_to_bv 64 fn));
    [ exact HFL | f_equal; rewrite length_le4; lia | first [reflexivity | vm_compute; reflexivity] | reflexivity
    | discriminate | lia | ].
  all: intros w1 q1 x14 x15 Hw1.
  all: assert (HM : bv_unsigned w1 = mix (bv_unsigned a0) (le32 fn))
         by (unfold mix, le32; rewrite Hw1; destruct (Z.eqb_spec (bv_unsigned a0) 0); try lia;
             rewrite ?unsigned_lit by (unfold FNV_B0; lia); reflexivity).
  all: clear Hw1.
  all: step.
  all: rewrite sx32_lit by lia.
  all: step.
  all: rewrite bv_lts_zero_l, unsigned_lit by lia.
  all: replace (Z.of_nat (length args) <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  all: rewrite andb_true_r.
  all: destruct (Z.ltb_spec 0 (Z.of_nat (length args))) as [N0|N0]; cbn [negb].
  2,4: eapply mix_exit with (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3)
         (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (F := F) (fc := fc)
         (m := m) (lo := lo) (h := bv_unsigned a0) (fn := fn) (args := args).
  all: try (destruct args; [rewrite HM; reflexivity | cbn [length] in N0; lia]).
  all: try eassumption.
  all: do 4 step.
  all: eapply (outer ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 F fc m lo (bv_unsigned a0) fn args STRLEN LO LA DH HARG
                 args 0%nat w1);
    [ reflexivity | destruct args; [cbn [length] in N0; lia | discriminate]
    | unfold mixcall; rewrite HM; reflexivity
    | first [reflexivity | vm_compute; reflexivity] | first [reflexivity | vm_compute; reflexivity]
    | first [reflexivity | vm_compute; reflexivity] | eassumption | eassumption | eassumption | eassumption | eassumption ].
Qed.
