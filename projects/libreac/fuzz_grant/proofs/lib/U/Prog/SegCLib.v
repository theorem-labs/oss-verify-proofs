From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma stk_cells : forall m lo hi a (n : nat),
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m lo hi a n H Ha Hn.
  destruct (stk_split rsegs m lo a hi H ltac:(lia)) as [_ H2].
  destruct (stk_split rsegs m a (a + Z.of_nat n) hi H2 ltac:(lia)) as [H3 _].
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n H3 ltac:(lia)) as [_ (junk & J)].
  exists junk. replace a with (a + Z.of_nat n - Z.of_nat n) at 1 by lia. exact J.
Qed.

Lemma rw_cells_CB_bytes : forall m A n bs,
  rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  split; [exact Hb|]. destruct Hwf as [Hl _]. exact Hl.
Qed.

Lemma bytes_byte_read : forall m A bs (i : nat),
  bytes_at rsegs m A bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m A bs i H Hi. rewrite (bytes_at_read rsegs m A bs (Z.of_nat i) 1 H) by lia.
  rewrite Nat2Z.id. rewrite (firstn1_skipn_nth bs i (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

Lemma Z_to_bv8_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma rd8_le : forall pl pos, (pos <= length pl)%nat ->
  (pos <= snd (rd8 pl pos) <= length pl)%nat.
Proof. intros pl pos H. unfold rd8. destruct (Nat.ltb_spec pos (length pl)); cbn; lia. Qed.

Lemma rd8_val : forall pl pos, 0 <= fst (rd8 pl pos) < 256.
Proof. intros pl pos. unfold rd8. destruct (pos <? length pl)%nat; cbn; [apply byte_range|lia]. Qed.

Lemma rd16_le : forall pl pos, (pos <= length pl)%nat ->
  (pos <= snd (rd16 pl pos) <= length pl)%nat.
Proof.
  intros pl pos H. unfold rd16.
  destruct (rd8 pl pos) as [lo p1] eqn:E1. pose proof (rd8_le pl pos H) as L1. rewrite E1 in L1. cbn in L1.
  destruct (rd8 pl p1) as [hi p2] eqn:E2. pose proof (rd8_le pl p1 ltac:(lia)) as L2. rewrite E2 in L2. cbn in L2.
  cbn. lia.
Qed.

Lemma header_pos_le : forall pl, (h_pos (header pl) <= length pl)%nat.
Proof.
  intros pl. unfold header.
  destruct (rd16 pl 0) as [u p1] eqn:E1. pose proof (rd16_le pl 0 ltac:(lia)) as L1. rewrite E1 in L1. cbn in L1.
  destruct (rd8 pl p1) as [i p2] eqn:E2. pose proof (rd8_le pl p1 ltac:(lia)) as L2. rewrite E2 in L2. cbn in L2.
  destruct (rd8 pl p2) as [r p3] eqn:E3. pose proof (rd8_le pl p2 ltac:(lia)) as L3. rewrite E3 in L3. cbn in L3.
  cbn. lia.
Qed.

Lemma cells_le : forall pl k pos, (pos <= length pl)%nat ->
  (pos <= snd (cells pl pos k) <= length pl)%nat.
Proof.
  intros pl k. induction k as [|k IH]; intros pos H; cbn [cells]; [cbn; lia|].
  destruct (rd8 pl pos) as [c p1] eqn:E1. pose proof (rd8_le pl pos H) as L1. rewrite E1 in L1. cbn in L1.
  destruct (rd8 pl p1) as [q p2] eqn:E2. pose proof (rd8_le pl p1 ltac:(lia)) as L2. rewrite E2 in L2. cbn in L2.
  destruct (rd8 pl p2) as [v p3] eqn:E3. pose proof (rd8_le pl p2 ltac:(lia)) as L3. rewrite E3 in L3. cbn in L3.
  destruct (cells pl p3 k) as [rest pe] eqn:E4. pose proof (IH p3 ltac:(lia)) as L4. rewrite E4 in L4. cbn in L4.
  cbn. lia.
Qed.

Lemma pos_cells_le : forall pl, (pos_cells pl <= length pl)%nat.
Proof. intros pl. unfold pos_cells. pose proof (rd8_le pl _ (header_pos_le pl)). lia. Qed.

Lemma pos_end_le : forall pl, (pos_end pl <= length pl)%nat.
Proof.
  intros pl. unfold pos_end, cells_upto. pose proof (cells_le pl (Z.to_nat (nset pl)) _ (pos_cells_le pl)). lia.
Qed.

Lemma raw_rd_0 : forall pl, pos_end pl = length pl -> raw_rd pl = (0, 0, pos_end pl).
Proof.
  intros pl H. assert (L : (pos_end pl <? length pl)%nat = false) by (apply Nat.ltb_ge; lia).
  unfold raw_rd, rd8. rewrite L. cbv beta iota zeta. rewrite L. reflexivity.
Qed.

Lemma raw_rd_1 : forall pl, S (pos_end pl) = length pl ->
  raw_rd pl = (pbz pl (pos_end pl), 0, length pl).
Proof.
  intros pl H. unfold raw_rd, rd8.
  rewrite (proj2 (Nat.ltb_lt (pos_end pl) (length pl))) by lia. cbv beta iota zeta.
  rewrite H, Nat.ltb_irrefl. reflexivity.
Qed.

Lemma raw_rd_2 : forall pl, (S (S (pos_end pl)) <= length pl)%nat ->
  raw_rd pl = (pbz pl (pos_end pl), pbz pl (S (pos_end pl)), S (S (pos_end pl))).
Proof.
  intros pl H. unfold raw_rd, rd8.
  rewrite (proj2 (Nat.ltb_lt (pos_end pl) (length pl))) by lia. cbv beta iota zeta.
  rewrite (proj2 (Nat.ltb_lt (S (pos_end pl)) (length pl))) by lia. reflexivity.
Qed.

Lemma rw_cells_two : forall m A a b,
  rw_cells rsegs m A [C1 a; C1 b] -> rw_cells rsegs m A [CB 2 [a; b]].
Proof.
  intros m A a b H. pose proof (rw_cells_merge rsegs m A [] [C1 a; C1 b] [] ) as M.
  cbn [app cells_size cells_bytes csize cbytes Nat.add] in M. apply M. exact H.
Qed.

Lemma rw_cells_prefix : forall m A n k bs,
  rw_cells rsegs m A [CB n bs] -> (k <= n)%nat -> rw_cells rsegs m A [CB k (firstn k bs)].
Proof.
  intros m A n k bs [[Hwf Hb] Hw] Hk. destruct Hwf as [Hl _]. cbn [cell_wf] in Hl.
  cbn [cells_bytes cbytes cells_size csize] in *. rewrite app_nil_r in Hb. rewrite ?Nat.add_0_r in Hw.
  split; [split|].
  - cbn. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
  - cbn [cells_size csize]. rewrite ?Nat.add_0_r. destruct Hw as (H1 & H2 & H3). split; [lia|]. split; [lia|].
    intros i Hi. apply H3. lia.
Qed.

Lemma LLVM_STACK_val : LLVM_STACK = 8800.
Proof. reflexivity. Qed.

Lemma LLVM_FRAME_val : LLVM_FRAME = 608.
Proof. reflexivity. Qed.

Definition frz (P : Prop) : Prop := P.
Lemma frz_in : forall P : Prop, P -> frz P.
Proof. intros P H. exact H. Qed.
Lemma frz_out : forall P : Prop, frz P -> P.
Proof. intros P H. exact H. Qed.

Lemma cells_size_map_C8 : forall l, cells_size (map C8 l) = (8 * length l)%nat.
Proof. induction l as [|v l IH]; cbn [map cells_size csize length]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal.
  apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    apply mod_mod8_of_modw. lia.
Qed.

Ltac unl := repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed64_small e) by lia
  end.
Ltac solve_cond2 := unfold_cond; fold_lit_ux; unl; solve_cond_rec.
Ltac ift := lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; solve_cond2] end.
Ltac iff_ := lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; solve_cond2] end.
Ltac ifc := first [ift | iff_].
Ltac stp := step; try (first [rewrite le1_zxb | rewrite le1_lit]; mem_after_store).
Ltac go pc_end := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif constr_eq pc pc_end then fail else stp
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifc
  end).

Lemma rg_MS_nz : forall R F pc fc rv m ro k, 1 <= k < 32 ->
  rg (MS R F pc fc rv m ro) k = Sem.reg_get R (Z_to_bv 5 k).
Proof.
  intros R F pc fc rv m ro k Hk. unfold rg, PropExec.getr. cbn [ms_regs MS].
  replace (bv_eqb (Z_to_bv 5 k) 0) with false; [reflexivity|].
  symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (bv_unsigned (0 : bv 5)) with 0. rewrite Z.mod_small by (cbn; lia). lia.
Qed.

Ltac rgs := rewrite rg_MS_nz by lia; simp_regs.

Ltac thaw1 H MU WM :=
  lazymatch type of MU with munch ?W ?m0 ?m1 =>
  lazymatch type of H with frz (rw_cells ?sg m0 ?A ?cs) =>
    apply frz_out in H;
    let D := fresh "D" in
    assert (D : disjoint_from W A (Z.of_nat (cells_size cs)))
      by (cbn [disjoint_from]; rewrite ?cells_size_map_C8, ?length_app, ?length_rev; simpl_sizes; slia);
    apply (rw_cells_transport sg W m0 m1 A cs H MU WM) in D; clear H; rename D into H
  end end.

Ltac thaw MU WM :=
  repeat match goal with H : frz (rw_cells _ _ _ _) |- _ => thaw1 H MU WM end.

Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac fin1 := rewrite ?LLVM_STACK_val, ?LLVM_FRAME_val in *; unfold w64;
  first [ reflexivity | assumption | lia | (rgs; first [reflexivity | f_equal; lia]) ].

Lemma zxb_lit8 : forall z, 0 <= z < 256 -> zxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.mod_small. cbn. lia.
Qed.

Lemma bs_res_ok : forall s al mx base w, s <> 0 -> al <> 0 -> fits base w = true -> 8 + 3 * w <= mx ->
  bs_res s al mx base w = 8 + 3 * w.
Proof.
  intros s al mx base w Hs Ha Hf Hm. unfold bs_res.
  rewrite (proj2 (Z.eqb_neq s 0)) by exact Hs. rewrite (proj2 (Z.eqb_neq al 0)) by exact Ha.
  rewrite Hf. cbn [orb negb]. rewrite (proj2 (Z.ltb_ge mx (8 + 3 * w))) by lia. reflexivity.
Qed.

Lemma bs_res_bad : forall s al mx base w, s = 0 \/ al = 0 \/ fits base w = false \/ mx < 8 + 3 * w ->
  bs_res s al mx base w = -1.
Proof.
  intros s al mx base w H. unfold bs_res.
  destruct H as [-> | [-> | [Hf | Hm]]].
  - reflexivity.
  - rewrite orb_true_r. reflexivity.
  - rewrite Hf. rewrite !orb_true_r. reflexivity.
  - destruct ((s =? 0) || (al =? 0) || negb (fits base w)); [reflexivity|].
    rewrite (proj2 (Z.ltb_lt mx (8 + 3 * w))) by lia. reflexivity.
Qed.

Lemma bs_win_ok : forall s al mx base w, bs_res s al mx base w = 8 + 3 * w -> 0 <= w ->
  bs_win s al mx base w = [(s, s + 34 * (8 + 3 * w))].
Proof.
  intros s al mx base w H Hw. unfold bs_win. rewrite H. rewrite (proj2 (Z.eqb_neq (8 + 3 * w) (-1))) by lia. reflexivity.
Qed.

Lemma bs_win_bad : forall s al mx base w, bs_res s al mx base w = -1 -> bs_win s al mx base w = [].
Proof. intros s al mx base w H. unfold bs_win. rewrite H. reflexivity. Qed.

Lemma fits_range : forall b w, fits b w = true -> 1 <= w <= 40 /\ 0 <= b /\ b + w <= 48.
Proof.
  intros b w H. unfold fits in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2, H3, H4. lia.
Qed.

Ltac side := first [ reflexivity | assumption
  | (unfold BUILD_SWEEP_STACK, CHECK_GROUPA_STACK; unl; first [ assumption | lia | (Z.div_mod_to_equations; lia) ]) ].

Ltac slia2 := repeat split; try exact I; lia.

Ltac xcall m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : rw_cells rsegs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  | H : bytes_at rsegs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  end;
  repeat match goal with
  | H : bytes_at rsegs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport rsegs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia2 ]
            | clear H ]
  | H : rw_cells rsegs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport rsegs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia2 ]
            | clear H ]
  | H : stk rsegs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint rsegs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia2 ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia2 | exact MU ] ]
  | H : wmono rsegs ?mq m |- _ => apply (wmono_trans rsegs mq m m') in H; [ | exact WM ]
  | H : mem_inv rsegs m |- _ => clear H
  end;
  clear MU WM.

Ltac retpc := lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Lemma rw_cells_two_inv : forall m A a b,
  rw_cells rsegs m A [CB 2 [a; b]] -> rw_cells rsegs m A [C1 a; C1 b].
Proof.
  intros m A a b [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - exact Hb.
  - exact Hw.
Qed.

Lemma lor_ones_w : forall y : word, Z.lor 18446744073709551615 (bv_unsigned y) = 18446744073709551615.
Proof.
  intros y. pose proof (bv_unsigned_in_range 64 y) as R. unfold bv_modulus in R.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z_lt_le_dec i 64) as [L|L].
  - change 18446744073709551615 with (Z.ones 64). rewrite Z.ones_spec_low by lia. reflexivity.
  - change 18446744073709551615 with (Z.ones 64). rewrite Z.ones_spec_high by lia. cbn [orb].
    apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec (bv_unsigned y) 0) as [E|E]; [rewrite E; cbn; lia|].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Ltac sltu_lit := repeat match goal with
  | |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (bv_unsigned (v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b))) in
      replace (v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac lit_fold := repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  end.
Ltac zn := sltu_lit; lit_fold; fold_lit_ux; rewrite ?Z.lor_0_l, ?lor_ones_w; rewrite ?zxb_lit8 by lia; unl;
  rewrite ?Z.shiftl_mul_pow2 by lia.

Ltac gz pc_end := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif constr_eq pc pc_end then fail else stp
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifc | (zn; ifc)]
  end).
