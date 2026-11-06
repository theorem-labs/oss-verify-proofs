From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import has_prefix_c next_line_c list_find_c RelayModel HarnessRep CheckRep.
Import ListNotations.
Open Scope Z_scope.

Definition ce_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (j : list byte) : list cell :=
  [CB 24 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ce_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ce_shl4 : forall n, 0 <= n < 2 ^ 26 -> Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 4 = 16 * n.
Proof. intros n Hn. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma ce_bzs_inj : forall a b, bzs a = bzs b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | exact (IH b H2)].
Qed.

Lemma ce_eqb_true : forall a b, list_eqb a b = true <-> a = b.
Proof. intros a b. unfold list_eqb. destruct (list_eq_dec Z.eq_dec a b); split; intros H; congruence. Qed.

Lemma ce_prefixb : forall P x, prefixb P x = true <-> prefix_of P x.
Proof.
  intros P x. unfold prefixb, prefix_of. rewrite andb_true_iff, Nat.leb_le, ce_eqb_true. split.
  - intros [H1 H2]. split; [exact H1 | exact (ce_bzs_inj _ _ H2)].
  - intros [H1 H2]. split; [exact H1 | rewrite H2; reflexivity].
Qed.

Lemma ce_firstn_S : forall {X} (l : list X) t x, nth_error l t = Some x -> firstn (S t) l = firstn t l ++ [x].
Proof.
  intros X l t x H. destruct (@nth_error_split X l t x H) as (l1 & l2 & -> & <-).
  rewrite (firstn_app (S (length l1))), (firstn_app (length l1)), (firstn_all2 l1) by lia.
  rewrite firstn_all, Nat.sub_diag. replace (S (length l1) - length l1)%nat with 1%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma ce_want_step : forall P rs t r, nth_error rs t = Some r ->
  want_of P (firstn (S t) rs) = (want_of P (firstn t rs) + (if prefixb P (snd r) then 1 else 0))%nat.
Proof.
  intros P rs t r H. unfold want_of. rewrite (ce_firstn_S rs t r H).
  rewrite list_basics.list.filter_app, length_app, list_basics.list.filter_singleton.
  destruct (decide _) as [D|D]; destruct (prefixb P (snd r)); cbn in *; try contradiction; try lia;
    exfalso; apply D; exact I.
  Unshelve. exact [].
Qed.

Lemma ce_swrap : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2 ^ 31) with 2147483648 in Hx. Z.div_mod_to_equations. lia.
Qed.

Lemma ce_want_le : forall P l, (want_of P l <= length l)%nat.
Proof.
  intros P l. unfold want_of. induction l as [|r l IH]; [reflexivity|].
  rewrite list_basics.list.filter_cons. destruct (decide _); cbn [length]; lia.
Qed.

Lemma ce_zxb : forall g, 0 <= g < 256 -> bv_unsigned (zxb (Z_to_bv 8 g)) = g.
Proof.
  intros g Hg. unfold zxb. rewrite Z_to_bv_unsigned, bv_wrap_small.
  - rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus. cbn. lia.
  - rewrite Z_to_bv_unsigned, bv_wrap_small; unfold bv_modulus; cbn; lia.
Qed.

Lemma ce_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma ce_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma ce_slt_pos : forall n, 0 < n < 2^31 -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 n) = Z_to_bv 64 1.
Proof.
  intros n H. unfold v_slt, c_lts, bv_lts. rewrite (ce_signed 0), (ce_signed n) by lia.
  rewrite (proj2 (Z.ltb_lt 0 n) ltac:(lia)). reflexivity.
Qed.

Lemma ce_and_mask : forall n, 0 <= n < 2^63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) (bv_unsigned (Z_to_bv 64 n))) =
  Z_to_bv 64 n.
Proof.
  intros n H. rewrite (unsigned_lit n) by lia.
  change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ce_sltu_pos : forall x : word, 0 < bv_unsigned x -> v_sltu (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof.
  intros x H. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0) by lia.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

Lemma ce_sltiu1 : forall w : word, 1 <= bv_unsigned w -> v_sltiu w 1 = Z_to_bv 64 0.
Proof.
  intros w H. unfold v_sltiu. change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned w) 1) H). reflexivity.
Qed.

Ltac ce_trap :=
  let HT := fresh "HT" in
  if_cases HT; [exfalso; zify_cond HT; rewrite ?ce_land7 in HT; Z.div_mod_to_equations; lia |]; clear HT.

Ltac ce_strap :=
  let HT := fresh "HT" in
  if_cases HT; [exfalso; unfold bv_lts in HT; rewrite ?ce_signed in HT by lia; zify_bool HT; lia |]; clear HT.

Ltac ce_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in
      lazymatch v with true => idtac | false => idtac end;
      change c with v; cbv iota
  end.

Lemma ce_epi : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (B : Z) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word)
    (j : list byte),
  sp = Z_to_bv 64 B -> 0 <= B -> B + 112 < 2 ^ 64 ->
  rw_cells rsegs m B (ce_frame rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v j) ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (B + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                                     s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
                              F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ba0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    B rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v j -> HB0 HB1 FR.
  unfold ce_frame in FR.
  do 13 step.
  apply evt_done. reflexivity.
Qed.

Lemma ce_pro : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (v : word) (n gone : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> 0x100000 <= lo -> mem_inv rsegs m ->
  0 < bv_unsigned a0 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 + 96 <= lo ->
  rw_cells rsegs m (bv_unsigned a0 + 80) [C8 v] -> rw_cells rsegs m (bv_unsigned a0 + 88) [C4 (Z_to_bv 64 n)] ->
  0 <= n < 2 ^ 26 -> (0 < n -> 0 < bv_unsigned v) ->
  rw_cells rsegs m 0x318a8 [C1 (Z_to_bv 8 gone)] -> 0 <= gone < 256 ->
  evt rsegs (fun ms' => exists m',
      munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      ((n = 0 /\ exists u0 u1 : word, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 u0 u1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)) \/
       (0 < n /\ exists j u0 u1, stk rsegs m' lo (bv_unsigned sp + -112) /\
          rw_cells rsegs m' (bv_unsigned sp + -112) (ce_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 j) /\
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 a1 (Z_to_bv 64 (bv_unsigned a0 + 80))
                        u0 u1 a2 a3 a4 a5 a6 a7 a2 (Z_to_bv 64 n) v (Z_to_bv 64 0) (Z_to_bv 64 n)
                        (Z_to_bv 64 (bv_unsigned v + 8)) (Z_to_bv 64 1) v s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x14ae8) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14a78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v n
    gone ST LO HI MI HA0 HA8 HA1 CV CN Hn HV GC Hg.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. cbn in Ra0.
  pose proof (bv_unsigned_in_range 64 v) as Rv. unfold bv_modulus in Rv. cbn in Rv.
  assert (G8 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 gone))) = gone) by exact (ce_zxb gone Hg).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 112%nat ST.
  do 12 step.
  step. ce_trap.
  step. step. step. ce_trap.
  step. step. rewrite (ce_sx32 n) by lia. step. step. step. if_cases Q.
  - zify_cond Q. assert (n = 0) by lia. subst n.
    step. step. step. if_cases Q2.
    + zify_cond Q2. rewrite G8 in Q2.
      step. step. ce_if.
      step. step. step. step. step. ce_if.
      do 13 step. apply evt_done. eexists.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      left. split; [reflexivity|]. do 2 eexists. reflexivity.
    + zify_cond Q2. rewrite G8 in Q2.
      step. step. ce_if.
      step. ce_if.
      do 13 step. apply evt_done. eexists.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      left. split; [reflexivity|]. do 2 eexists. reflexivity.
  - zify_cond Q. specialize (HV ltac:(lia)).
    do 7 step.
    rewrite (ce_slt_pos n), (ce_and_mask n), (ce_sltu_pos v) by lia.
    apply evt_done. eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. split; [lia|]. do 3 eexists. split; [eassumption|]. split; [exact FR|]. reflexivity.
Qed.

Lemma ce_count : has_prefix_contract ->
  forall (rs : list (Z * list byte)) (P slack : list byte) (c t : nat) (V PF : Z)
    (ra sp gp tp t0 t1 t2 s1 s2 s3 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w4 w7 w9 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  c = (length rs - t)%nat -> (t < length rs)%nat ->
  bv_unsigned w4 = V -> bv_unsigned w7 = V + 8 + 16 * Z.of_nat t -> bv_unsigned w9 = V + 16 * Z.of_nat t ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> mem_inv rsegs m ->
  0 < V -> V mod 8 = 0 -> V + 16 * Z.of_nat (length rs) + 8 < 2 ^ 63 -> Z.of_nat (length rs) < 2 ^ 26 ->
  V + 16 * Z.of_nat (length rs) <= bv_unsigned sp - 32 ->
  (forall k r, nth_error rs k = Some r ->
     rw_cells rsegs m (V + 16 * Z.of_nat k) [C8 (Z_to_bv 64 (fst r)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r))))] /\
     bytes_at rsegs m (fst r) (snd r) /\ 0 <= fst r /\ fst r + Z.of_nat (length (snd r)) <= bv_unsigned sp - 32) ->
  bytes_at rsegs m PF (P ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) P ->
  (- (PF + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 <= PF -> PF < 2 ^ 64 ->
  (PF + Z.of_nat (length P + 1 + length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= PF) ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s6' s7' s9' m',
      ms' = MS (mkR (Z_to_bv 64 0x14b14) sp gp tp t0' t1' t2' (Z_to_bv 64 PF) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3
                    w4 (Z_to_bv 64 (Z.of_nat (want_of P rs))) s6' s7' (Z_to_bv 64 1) s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14b34) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 PF) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 w4
             (Z_to_bv 64 (Z.of_nat (want_of P (firstn t rs)))) (Z_to_bv 64 (Z.of_nat c)) w7 (Z_to_bv 64 1) w9
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ae8) fc None m (seg_rom rsegs)).
Proof.
  intros HP rs P slack c. induction c as [|c IH]; intros t V PF ra sp gp tp t0 t1 t2 s1 s2 s3 s10 s11
    a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w4 w7 w9 F fc m lo Hc Ht H4 H7 H9 ST LO MI HV0 HV8 HV1 HN HVS RS HPB NZ SL
    HPF0 HPF1 HPD; [lia|].
  destruct (nth_error rs t) as [r|] eqn:Hr; [|apply nth_error_None in Hr; lia].
  destruct (RS t r Hr) as (RC & RB & R0 & R1).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  replace (V + 16 * Z.of_nat t) with (bv_unsigned w7 + -8) in RC by lia.
  pose proof (ce_want_le P (firstn t rs)) as WL. rewrite length_firstn in WL.
  step. ce_trap.
  step. rewrite (ce_sltiu1 w9) by lia. step. step. if_false.
  step. ce_trap.
  step. step. ce_trap.
  step. step. step. step.
  assert (U1 : bv_unsigned (Z_to_bv 64 (fst r)) = fst r) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (snd r)))) = Z.of_nat (length (snd r)))
    by (apply unsigned_lit; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 PF) = PF) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply HP with (lo := lo) (S := snd r) (P := P) (slack := slack); rewrite ?U1, ?U2, ?U3.
    - exact RB.
    - reflexivity.
    - exact HPB.
    - exact NZ.
    - exact SL.
    - exact MI.
    - exact ST.
    - exact LO.
    - unfold HAS_PREFIX_K. left. lia.
    - exact HPD. }
  intros ms' (u0 & u1 & u2 & b0 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 &
    -> & MU1 & WM1 & MI1 & ST1 & PR).
  unfold HAS_PREFIX_K in MU1.
  replace (ret_pc (Z_to_bv 64 0x14b14)) with (Z_to_bv 64 0x14b14) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (RS1 : forall k r, nth_error rs k = Some r ->
    rw_cells rsegs m1 (V + 16 * Z.of_nat k) [C8 (Z_to_bv 64 (fst r)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r))))] /\
    bytes_at rsegs m1 (fst r) (snd r) /\ 0 <= fst r /\ fst r + Z.of_nat (length (snd r)) <= bv_unsigned sp - 32).
  { intros k r' Hk. destruct (RS k r' Hk) as (X1 & X2 & X3 & X4).
    pose proof (proj1 (nth_error_Some rs k) ltac:(rewrite Hk; discriminate)) as Hkl.
    split; [|split; [|split; [exact X3 | exact X4]]].
    - apply (rw_cells_transport rsegs _ m m1 _ _ X1 MU1 WM1). cbn [disjoint_from cells_size csize]. split; [lia | exact I].
    - apply (bytes_at_transport rsegs _ m m1 _ _ X2 MU1). cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HPB1 : bytes_at rsegs m1 PF (P ++ Z_to_bv 8 0 :: slack)).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HPB MU1). cbn [disjoint_from]. rewrite length_app. cbn [length].
    split; [lia | exact I]. }
  eapply (evt_cut rsegs (fun ms => exists a0x : word,
    ms = MS (mkR (Z_to_bv 64 0x14b14) sp gp tp u0 u1 u2 (Z_to_bv 64 PF) s1 a0x u3 u4 u5 u6 u7 u8 u9 s2 s3 w4
               (Z_to_bv 64 (Z.of_nat (want_of P (firstn (S t) rs)))) (Z_to_bv 64 (Z.of_nat (S c))) w7 (Z_to_bv 64 1) w9
               s10 s11 u10 u11 u12 u13) F (Z_to_bv 64 0x14b24) fc None m1 (seg_rom rsegs))).
  { destruct PR as [(PO & ->)|(PO & ->)].
    - assert (WF1 : Z.of_nat (want_of P (firstn (S t) rs)) = Z.of_nat (want_of P (firstn t rs)) + 1)
        by (rewrite (ce_want_step P rs t r Hr), (proj2 (ce_prefixb P (snd r)) PO); lia).
      step. if_false. step. rewrite (unsigned_lit (Z.of_nat (want_of P (firstn t rs)))), ce_swrap by lia.
      step. ce_strap. step.
      apply evt_done. eexists. rewrite WF1. reflexivity.
    - destruct (prefixb P (snd r)) eqn:E; [exfalso; apply PO; apply ce_prefixb; exact E|].
      assert (WF0 : Z.of_nat (want_of P (firstn (S t) rs)) = Z.of_nat (want_of P (firstn t rs)))
        by (rewrite (ce_want_step P rs t r Hr), E; lia).
      step. if_true.
      apply evt_done. eexists. rewrite WF0. reflexivity. }
  intros ms2 (a0x & ->).
  step. step. step. step. if_cases Q.
  - zify_cond Q.
    replace (Z.of_nat (S c) + -1) with (Z.of_nat c) by lia.
    eapply evt_mono.
    { eapply (IH (S t) V PF); try eassumption; try lia; rewrite unsigned_lit by lia; lia. }
    intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & m2 &
      -> & MU2 & WM2 & MI2 & ST2).
    do 18 eexists. exists m2. split; [reflexivity|].
    split; [exact (munch_trans _ _ _ _ MU1 MU2)|]. split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
    split; [exact MI2 | exact ST2].
  - zify_cond Q. assert (Ht1 : S t = length rs) by (Z.div_mod_to_equations; lia).
    rewrite Ht1, firstn_all.
    apply evt_done. do 18 eexists. exists m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1 | exact ST1].
Qed.

Lemma ce_mid : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (B n W gone : Z)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word) (j : list byte),
  sp = Z_to_bv 64 B -> 0 <= B -> B + 112 < 2 ^ 64 -> mem_inv rsegs m ->
  rw_cells rsegs m B (ce_frame rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v j) ->
  rw_cells rsegs m 0x318a8 [C1 (Z_to_bv 8 gone)] -> 0 <= gone < 256 ->
  0 < n < 2 ^ 26 -> 0 <= W < 2 ^ 26 ->
  evt rsegs (fun ms' =>
      (gone <> 0 /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (n - 1)) a1 a2 a3 a4 a5 a6 a7 s2
                               (Z_to_bv 64 n) s4 (Z_to_bv 64 W) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x14b4c) fc None m (seg_rom rsegs)) \/
      (gone = 0 /\ W = 0 /\ exists a0' a1',
         ms' = MS (mkR rav (Z_to_bv 64 (B + 112)) gp tp t0 t1 t2 s0v s1v a0' a1' a2 a3 a4 a5 a6 a7
                       s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m (seg_rom rsegs)) \/
      (gone = 0 /\ 0 < W /\ exists a0' a1',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n)
                       (Z_to_bv 64 4) (Z_to_bv 64 W) (Z_to_bv 64 5) (Z_to_bv 64 0x646e6520) (Z_to_bv 64 (W - 1))
                       s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x14bf4) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 (Z_to_bv 64 W) s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b34) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B n W gone
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v j -> HB0 HB1 MI FR GG Hg Hn HW.
  assert (G8 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 gone))) = gone) by exact (ce_zxb gone Hg).
  step. step. step. if_cases Q.
  - zify_cond Q. rewrite G8 in Q.
    step. rewrite (unsigned_lit W), ce_swrap by lia. step. ce_strap.
    step. step. step. step. step. if_cases Q2.
    + zify_cond Q2. unfold ce_frame in FR. do 13 step. apply evt_done. right. left.
      split; [lia|]. split; [lia|]. do 2 eexists. reflexivity.
    + zify_cond Q2. step. apply evt_done. right. right.
      split; [lia|]. split; [lia|]. replace (W + -1) with (W - 1) by lia. do 2 eexists. reflexivity.
  - zify_cond Q. rewrite G8 in Q.
    step. rewrite (unsigned_lit n), ce_swrap by lia. step. ce_strap.
    step. if_cases Q2; [exfalso; zify_cond Q2; lia|].
    apply evt_done. left. split; [lia|]. replace (n + -1) with (n - 1) by lia. reflexivity.
Qed.
