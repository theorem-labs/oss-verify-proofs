From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandFP CommandTac printf_facts_c atoi_c snprintf_c strcmp_c check_words_chain_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma mod64_32 : forall a, (a mod 2^64) mod 2^32 = a mod 2^32.
Proof.
  intros a. rewrite (Z.div_mod a (2^64)) at 2 by lia.
  replace (2^64 * (a / 2^64)) with ((a / 2^64 * 2^32) * 2^32) by ring.
  rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.

Definition pfc (c : Z) : Prop := 0 < c < 256.

Lemma pf_digits_len : forall f x acc j, 0 <= x < 10 ^ Z.of_nat j -> (1 <= j)%nat ->
  (length (pf_digits f x acc) <= j + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc j Hx Hj; cbn [pf_digits]; [lia|].
  destruct (Z.ltb_spec x 10) as [L|L].
  - cbn [length]. lia.
  - destruct j as [|[|j]]; [lia| |].
    + exfalso. assert (E : 10 ^ Z.of_nat 1 = 10) by reflexivity. lia.
    + assert (B : 0 <= x / 10 < 10 ^ Z.of_nat (S j)).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
        replace (Z.of_nat (S (S j))) with (Z.of_nat (S j) + 1) in Hx by lia.
        rewrite Z.pow_add_r, Z.pow_1_r in Hx by lia. lia. }
      specialize (IH (x / 10) ((48 + x mod 10) :: acc) (S j) B ltac:(lia)).
      cbn [length] in IH. lia.
Qed.

Lemma pf_dec_len : forall v, -2^31 <= v < 2^31 -> (length (pf_dec v) <= 11)%nat.
Proof.
  intros v Hv. unfold pf_dec.
  assert (E : 10 ^ Z.of_nat 10 = 10000000000) by reflexivity.
  destruct (Z.ltb_spec v 0).
  - pose proof (pf_digits_len 11 (- v) [] 10 ltac:(lia) ltac:(lia)) as HL. cbn [length] in *. lia.
  - pose proof (pf_digits_len 11 v [] 10 ltac:(lia) ltac:(lia)) as HL. cbn [length] in *. lia.
Qed.

Lemma pf_digits_nz : forall f x acc, 0 <= x -> Forall pfc acc -> Forall pfc (pf_digits f x acc).
Proof.
  induction f as [|f IH]; intros x acc Hx Ha; cbn [pf_digits]; [exact Ha|].
  destruct (Z.ltb_spec x 10).
  - constructor; [unfold pfc; lia | exact Ha].
  - apply IH; [apply Z.div_pos; lia|]. constructor; [|exact Ha].
    unfold pfc. pose proof (Z.mod_pos_bound x 10 ltac:(lia)). lia.
Qed.

Lemma pf_dec_nz : forall v, Forall pfc (pf_dec v).
Proof.
  intros v. unfold pf_dec. destruct (Z.ltb_spec v 0).
  - constructor; [unfold pfc; lia|]. apply pf_digits_nz; [lia | constructor].
  - apply pf_digits_nz; [lia | constructor].
Qed.

Lemma atoi_acc_range : forall s n, -2^31 <= n < 2^31 -> -2^31 <= atoi_acc n s < 2^31.
Proof.
  induction s as [|b s IH]; intros n Hn; cbn [atoi_acc]; [exact Hn|].
  destruct (c_digit b); [apply IH, swrap32_range | exact Hn].
Qed.

Lemma atoi_val_range : forall s, -2^31 <= atoi_val s < 2^31.
Proof.
  intros s. unfold atoi_val. destruct (skip_space s) as [|b r0]; [lia|].
  destruct (_ =? 45); [apply atoi_acc_range; lia|].
  destruct (_ =? 43); apply swrap32_range.
Qed.

Definition citem (k : nat) (ws : list (list byte)) : list Z :=
  (if Nat.eqb k 2 then [] else [32]) ++ pf_dec (atoi_val (nth k ws [])).

Lemma chain_items_S : forall n k ws, chain_items k (S n) ws = citem k ws ++ chain_items (S k) n ws.
Proof. intros n k ws. cbn [chain_items]. unfold citem. rewrite <- app_assoc. reflexivity. Qed.

Lemma chain_items_snoc : forall n k ws, chain_items k (S n) ws = chain_items k n ws ++ citem (k + n) ws.
Proof.
  induction n as [|n IH]; intros k ws.
  - rewrite chain_items_S. cbn [chain_items app]. rewrite Nat.add_0_r, app_nil_r. reflexivity.
  - rewrite (chain_items_S (S n) k ws), (IH (S k) ws), (chain_items_S n k ws), app_assoc.
    replace (S k + n)%nat with (k + S n)%nat by lia. reflexivity.
Qed.

Lemma citem_len : forall k ws, (length (citem k ws) <= 12)%nat.
Proof.
  intros k ws. unfold citem. rewrite length_app.
  pose proof (pf_dec_len _ (atoi_val_range (nth k ws []))).
  destruct (Nat.eqb k 2); cbn [length]; lia.
Qed.

Lemma chain_items_len : forall n k ws, (length (chain_items k n ws) <= 12 * n)%nat.
Proof.
  induction n as [|n IH]; intros k ws; [cbn; lia|].
  rewrite chain_items_S, length_app. pose proof (citem_len k ws). specialize (IH (S k) ws). lia.
Qed.

Lemma citem_nz : forall k ws, Forall pfc (citem k ws).
Proof.
  intros k ws. unfold citem. apply Forall_app. split; [|apply pf_dec_nz].
  destruct (Nat.eqb k 2); repeat constructor; unfold pfc; lia.
Qed.

Lemma chain_items_nz : forall n k ws, Forall pfc (chain_items k n ws).
Proof.
  induction n as [|n IH]; intros k ws; [constructor|].
  rewrite chain_items_S. apply Forall_app. split; [apply citem_nz | apply IH].
Qed.

Lemma notin_nul_pf : forall l, Forall pfc l -> ~ In (Z_to_bv 8 0) (pf_bytes l).
Proof.
  intros l H Hin. unfold pf_bytes in Hin. apply in_map_iff in Hin. destruct Hin as (c & E & Hc).
  rewrite Forall_forall in H. specialize (H c Hc). unfold pfc in H.
  apply (f_equal (@bv_unsigned 8)) in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
  rewrite Z.mod_small in E by lia. rewrite Zmod_0_l in E. lia.
Qed.

Lemma pf_bytes_nul : forall l, pf_bytes (l ++ [0]) = pf_bytes l ++ [Z_to_bv 8 0].
Proof. intros l. unfold pf_bytes. rewrite map_app. reflexivity. Qed.

Lemma length_pf_bytes : forall l, length (pf_bytes l) = length l.
Proof. intros l. unfold pf_bytes. apply length_map. Qed.

Lemma wr_at_sub : forall m A n k n', wr_at rsegs m A n -> 0 <= k -> 0 <= n' -> k + n' <= n -> wr_at rsegs m (A + k) n'.
Proof.
  intros m A n k n' (Ha & Hn & H) Hk Hn' Hkn. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_cbn : forall m A n bs, bytes_at rsegs m A bs -> wr_at rsegs m A (Z.of_nat n) -> length bs = n ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m A n bs Hb Hw Hl. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma rw_cells_cb_inv : forall m A n bs, rw_cells rsegs m A [CB n bs] ->
  bytes_at rsegs m A bs /\ wr_at rsegs m A (Z.of_nat n) /\ length bs = n.
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf.
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. rewrite app_nil_r in Hb. rewrite Nat.add_0_r in Hw. tauto.
Qed.

Lemma wr_at_app : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (Ha & Hn & H) H1 H2.
  split; (split; [lia | split; [lia|]]); intros i Hi; [apply H; lia|].
  replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply wr_at_app in Hw; [|lia|lia]. destruct Hw as [Hw1 Hw2].
  split; split; try (split; assumption); assumption.
Qed.

Lemma skipn_pf : forall L jl, skipn (length L) (pf_bytes (L ++ [0]) ++ jl) = Z_to_bv 8 0 :: jl.
Proof.
  intros L jl. rewrite pf_bytes_nul, <- app_assoc, <- (length_pf_bytes L), skipn_app_exact. reflexivity.
Qed.

Lemma bytes_at_app3 : forall m a l1 l2 l3 b c, bytes_at rsegs m a l1 -> bytes_at rsegs m b l2 -> bytes_at rsegs m c l3 ->
  b = a + Z.of_nat (length l1) -> c = b + Z.of_nat (length l2) -> bytes_at rsegs m a (l1 ++ l2 ++ l3).
Proof.
  intros m a l1 l2 l3 b c H1 H2 H3 -> ->. apply bytes_at_app. split; [exact H1|].
  apply bytes_at_app. split; assumption.
Qed.

Lemma pf_bytes_snoc : forall L T, pf_bytes ((L ++ T) ++ [0]) = pf_bytes L ++ pf_bytes (T ++ [0]).
Proof. intros L T. unfold pf_bytes. rewrite <- app_assoc, map_app. reflexivity. Qed.

Lemma frame_split : forall mc A j0 v j1 b j2 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13,
  rw_cells rsegs mc A [CB 8 j0; C8 v; CB 23 j1; C1 b; CB 768 j2; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6;
                       C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  exists ja jb, rw_cells rsegs mc A [CB 8 j0; C8 v; CB 7 ja] /\ rw_cells rsegs mc (A + 23) [CB 16 jb] /\
    bytes_at rsegs mc (A + 39) (b :: j2) /\ length j2 = 768%nat /\ wr_at rsegs mc (A + 39) 769 /\
    rw_cells rsegs mc (A + 808) [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13].
Proof.
  intros mc A j0 v j1 b j2 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 H.
  change (rw_cells rsegs mc A ([CB 8 j0; C8 v; CB 23 j1] ++ [C1 b; CB 768 j2] ++
            [C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13])) in H.
  apply rw_cells_app in H. destruct H as [H1 H23]. apply rw_cells_app in H23. destruct H23 as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3.
  apply (rw_cells_cb_split rsegs mc A _ [CB 8 j0; C8 v; CB 7 (firstn 7 j1); CB 16 (firstn 16 (skipn 7 j1))] 23 16) in H1;
    [| reflexivity | reflexivity].
  change (rw_cells rsegs mc A ([CB 8 j0; C8 v; CB 7 (firstn 7 j1)] ++ [CB 16 (firstn 16 (skipn 7 j1))])) in H1.
  apply rw_cells_app in H1. destruct H1 as [H1a H1b]. cbn [cells_size csize Nat.add] in H1b.
  destruct H2 as [[W2 B2] Wr2]. cbn [cells_wf cell_wf] in W2. cbn [cells_bytes cbytes cells_size csize Nat.add] in B2, Wr2.
  rewrite app_nil_r in B2.
  exists (firstn 7 j1), (firstn 16 (skipn 7 j1)).
  split; [exact H1a|]. split; [exact H1b|]. split; [exact B2|]. split; [tauto|]. split; [exact Wr2|].
  replace (A + 808) with (A + Z.of_nat 39 + Z.of_nat 769) by lia. exact H3.
Qed.

Lemma slot_transport : forall m mc lo S A p s,
  word_slot m lo S A p s -> munch [(lo, S)] m mc ->
  bytes_at rsegs mc A (le8 p) /\ bytes_at rsegs mc (bv_unsigned p) (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s.
Proof.
  intros m mc lo S A p s (H1 & D1 & [H2 N2] & D2) MU. unfold outside_stack in D1, D2.
  split; [|split; [|exact N2]].
  - eapply bytes_at_transport; [exact H1 | exact MU | rewrite length_le8; exact D1].
  - eapply bytes_at_transport; [exact H2 | exact MU |].
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D2.
Qed.

Lemma rsegs_top : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x55000) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_free_hi : forall D n, 0x55000 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs. pose proof rsegs_top as T. rewrite forallb_forall in T.
  specialize (T s Hs). apply Z.leb_le in T. pose proof (bv_unsigned_in_range 64 (snd s)). lia.
Qed.

Lemma task_mem_munch : forall m m' lo hi, MemNorm.task_mem rsegs m -> stk rsegs m lo hi ->
  munch [(lo, hi)] m m' -> MemNorm.task_mem rsegs m'.
Proof.
  intros m m' lo hi TM (_ & _ & HS) MU a b E.
  destruct (Z_lt_le_dec (bv_unsigned a) lo) as [L|L]; [|destruct (Z_lt_le_dec (bv_unsigned a) hi) as [H|H]].
  2: { destruct (HS (bv_unsigned a) (conj L H)) as [W _]. unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
       destruct (m a) as [b'|] eqn:Ea; [exact (TM a b' Ea)|].
       unfold wview in W. rewrite Ea in W.
       destruct (find_segment rsegs (bv_unsigned a) 1) as [s|]; [left; discriminate | contradiction]. }
  all: rewrite (MU a) in E; [exact (TM a b E) | cbn [outside]; split; [lia | exact I]].
Qed.

Section Chain.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
  (m : word -> option byte) (lo r : Z) (wp : list word) (ws : list (list byte)) (p1 p2 : word)
  (x1 x2 : list byte) (can : word).
Hypothesis ATOI : atoi_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis SC : strcmp_contract.
Hypothesis LO : lo + 6848 <= bv_unsigned sp.
Hypothesis IE : CommandModel.IMG_END <= lo.
Hypothesis SPH : bv_unsigned sp < 2^63.
Hypothesis GG : rw_cells rsegs m CommandModel.GOT_GUARD [C8 (Z_to_bv 64 CommandModel.GUARD)].
Hypothesis GU : rw_cells rsegs m CommandModel.GUARD [C8 can].
Hypothesis TMW : forall mc, munch [(lo, bv_unsigned sp)] m mc -> MemNorm.task_mem rsegs mc.
Hypothesis RR : 0 <= r <= 64.
Hypothesis HW : forall k, 2 <= k < r ->
  word_slot m lo (bv_unsigned sp) (bv_unsigned a1 + 8 * k) (nth (Z.to_nat k) wp (Z_to_bv 64 0)) (nth (Z.to_nat k) ws []).
Hypothesis HN : bytes_at rsegs m (bv_unsigned a0 + CALL_NARGS) (le4 (Z_to_bv 64 3)).
Hypothesis HND : outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + CALL_NARGS) 4.
Hypothesis HP1 : word_slot m lo (bv_unsigned sp) (bv_unsigned a0 + CALL_ARGS + 8) p1 x1.
Hypothesis HP2 : word_slot m lo (bv_unsigned sp) (bv_unsigned a0 + CALL_ARGS + 16) p2 x2.
Hypothesis X1 : x1 = pf_bytes (pf_dec (r - 2)).
Hypothesis X2 : x2 = pf_bytes (chain_list r ws).

Lemma rw_cells_c8_bytes : forall mc A v, rw_cells rsegs mc A [C8 v] -> bytes_at rsegs mc A (le8 v).
Proof. intros mc A v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma guards_at : forall mc, munch [(lo, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  bytes_at rsegs mc snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) /\ bytes_at rsegs mc snprintf_c.GUARD (le8 can).
Proof.
  intros mc MU WM. unfold CommandModel.IMG_END in IE.
  split.
  - apply rw_cells_c8_bytes. eapply rw_cells_transport; [exact GG | exact MU | exact WM |].
    cbn [disjoint_from cells_size csize]. unfold snprintf_c.GOT_GUARD. split; [lia | exact I].
  - apply rw_cells_c8_bytes. eapply rw_cells_transport; [exact GU | exact MU | exact WM |].
    cbn [disjoint_from cells_size csize]. unfold snprintf_c.GUARD. split; [lia | exact I].
Qed.

Lemma args_at : forall mc, munch [(lo, bv_unsigned sp)] m mc ->
  ro_cells rsegs mc (bv_unsigned a0 + 4) [C4 (Z_to_bv 64 3)] /\
  ro_cells rsegs mc (bv_unsigned a0 + 16) [C8 p1] /\
  bytes_at rsegs mc (bv_unsigned p1) (x1 ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) x1 /\
  ro_cells rsegs mc (bv_unsigned a0 + 24) [C8 p2] /\
  bytes_at rsegs mc (bv_unsigned p2) (x2 ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) x2.
Proof.
  intros mc MU.
  destruct (slot_transport _ _ _ _ _ _ _ HP1 MU) as (S1 & B1 & N1).
  destruct (slot_transport _ _ _ _ _ _ _ HP2 MU) as (S2 & B2 & N2).
  unfold CALL_ARGS in S1, S2. replace (bv_unsigned a0 + 8 + 8) with (bv_unsigned a0 + 16) in S1 by lia.
  replace (bv_unsigned a0 + 8 + 16) with (bv_unsigned a0 + 24) in S2 by lia.
  assert (H4 : bytes_at rsegs mc (bv_unsigned a0 + 4) (le4 (Z_to_bv 64 3))).
  { eapply bytes_at_transport; [exact HN | exact MU |]. unfold outside_stack in HND.
    rewrite length_le4. exact HND. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
    first [apply bytes_ro4; assumption | apply bytes_ro8; assumption | assumption].
Qed.

Ltac tp_cells MU WM H :=
  lazymatch type of MU with munch ?W ?m1 ?m2 =>
    apply (rw_cells_transport rsegs W m1 m2) in H; [ | exact MU | exact WM | cbn [disjoint_from cells_size csize]; first [exact I | lia] ]
  end.
Ltac tp_bytes MU H :=
  lazymatch type of MU with munch ?W ?m1 ?m2 =>
    apply (bytes_at_transport rsegs W m1 m2) in H;
    [ | exact MU | cbn [disjoint_from]; rewrite ?length_app, ?length_pf_bytes, ?length_app, ?length_skipn; cbn [length]; first [exact I | lia] ]
  end.
Ltac tp_munch MU MU2 :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of MU2 with munch ?W2 _ ?mc =>
    apply (munch_trans W ma mb mc) in MU;
    [ | apply (munch_weaken W2 W mb mc); [ unfold sub_fp; cbn [outside]; intros ? [? _]; repeat split; lia | exact MU2 ] ]
  end end.

Lemma fp_chain : forall (Fc Ft : bvmap 5 word),
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get Fc k) ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k).
Proof. intros Fc Ft H1 H2 k Hk. rewrite H2 by exact Hk. apply H1. exact Hk. Qed.

Lemma tail : forall mc Fc fcc j0 j1 jb jl rac t0c t1c t2c s0c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c
    a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  mem_inv rsegs mc -> munch [(lo, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -912) -> frm0 fcc ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
  rw_cells rsegs mc (bv_unsigned sp + -912) [CB 8 j0; C8 a0; CB 7 j1] ->
  rw_cells rsegs mc (bv_unsigned sp + -889) [CB 16 jb] ->
  bytes_at rsegs mc (bv_unsigned sp + -873) (pf_bytes (chain_list r ws ++ [0]) ++ jl) ->
  wr_at rsegs mc (bv_unsigned sp + -873) 769 ->
  Z.of_nat (length (chain_list r ws)) + 1 + Z.of_nat (length jl) = 769 ->
  rw_cells rsegs mc (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs (fp_void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo m)
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -912)) gp tp t0c t1c t2c s0c (Z_to_bv 64 r)
             a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c t3c t4c t5c t6c)
        Fc (Z_to_bv 64 0x152d8) fcc None mc (seg_rom rsegs)).
Proof.
  intros mc Fc fcc j0 j1 jb jl rac t0c t1c t2c s0c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c
    a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c MI MU WM ST FRM FP FRA BUF LIST LW LL FRH.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold CommandModel.IMG_END in IE.
  do 6 zstep.
  assert (SW : bv_swrap 32 (r + -2) = r - 2).
  { unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
    change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia. }
  rewrite SW.
  pose proof (pf_dec_len (r - 2) ltac:(lia)) as TL.
  destruct (guards_at mc MU WM) as [G1 G2].
  destruct (rw_cells_cb_inv _ _ _ _ BUF) as (BB & BW & BL).
  pose proof (bytes_at_skipn _ _ _ (S (length (pf_dec (r - 2)))) BB ltac:(lia)) as BT.
  clear BB.
  eapply evt_cut.
  { eapply SNP with (fmt := [37; 100]) (ps := [Pd]) (args := [AInt (r - 2)]) (T := pf_dec (r - 2))
                    (junk := jb) (lo := lo) (canary := can).
    - rewrite unsigned_lit by lia. apply lit_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia].
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END. cbn [length Z.of_nat]. lia.
    - reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [lia|].
      rewrite unsigned_lit_wrap. apply mod64_32.
    - cbn [pf_text option_map]. rewrite app_nil_r. reflexivity.
    - rewrite !unsigned_lit by lia. exact BUF.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite !unsigned_lit by lia. lia.
    - right. rewrite !unsigned_lit by lia. lia.
    - apply img_free_hi. rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - unfold snprintf_c.IMG_END. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact MI.
    - exact (TMW mc MU).
    - exact G1.
    - exact G2. }
  intros ms' PO. unfold printf_post in PO. rewrite !unsigned_lit in PO by lia.
  rewrite firstn_all2 in PO by lia.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m2 &
                  E & MU2 & WM2 & MI2 & _ & FRM2 & FP2 & ST2 & DB2).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 86768)) with (Z_to_bv 64 86768) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (fp_chain Fc Ft FP FP2) as FP3. clear FP FP2.
  tp_cells MU2 WM2 FRA.
  tp_cells MU2 WM2 FRH.
  tp_bytes MU2 LIST.
  tp_bytes MU2 BT.
  apply (wr_at_transport rsegs mc m2) in LW; [|exact WM2].
  apply (wr_at_transport rsegs mc m2) in BW; [|exact WM2].
  tp_munch MU MU2.
  pose proof (wmono_trans rsegs m mc m2 WM WM2) as WM3.
  clear MU2 WM2 WM G1 G2 MI BUF ST.
  assert (BUF2 : rw_cells rsegs m2 (bv_unsigned sp + -889)
                   [CB 16 (pf_bytes (pf_dec (r - 2) ++ [0]) ++ skipn (S (length (pf_dec (r - 2)))) jb)]).
  { apply rw_cells_cbn; [| exact BW |].
    - apply bytes_at_app. split; [exact DB2|].
      rewrite length_pf_bytes, length_app. cbn [length]. rewrite Nat.add_1_r. exact BT.
    - rewrite length_app, length_pf_bytes, length_app, length_skipn. cbn [length]. lia. }
  clear BT BW.
  destruct (args_at m2 MU) as (RN & RP1 & BP1 & NP1 & RP2 & BP2 & NP2).
  assert (SY1 : bytes_at rsegs m2 (bv_unsigned sp + -889) (pf_bytes (pf_dec (r - 2)) ++ [Z_to_bv 8 0]))
    by (rewrite <- pf_bytes_nul; exact DB2).
  assert (SY2 : bytes_at rsegs m2 (bv_unsigned sp + -873) (pf_bytes (chain_list r ws) ++ [Z_to_bv 8 0])).
  { rewrite <- pf_bytes_nul. apply bytes_at_app in LIST. exact (proj1 LIST). }
  assert (LC : rw_cells rsegs m2 (bv_unsigned sp + -873) [CB 769 (pf_bytes (chain_list r ws ++ [0]) ++ jl)]).
  { apply rw_cells_cbn; [exact LIST | exact LW |].
    rewrite length_app, length_pf_bytes, length_app. cbn [length]. lia. }
  clear LIST LW DB2.
  zstep. zstep. zstep. zstep.
  if_cases HNE.
  - exfalso. vm_compute in HNE. discriminate HNE.
  - zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SC with (sx := x1) (sy := pf_bytes (pf_dec (r - 2))).
      - exact BP1.
      - exact NP1.
      - rewrite unsigned_lit by lia. exact SY1.
      - apply notin_nul_pf, pf_dec_nz. }
    intros ms' (rr & x11 & x12 & x13 & E & Hrr). subst ms'.
    replace (ret_pc (Z_to_bv 64 86796)) with (Z_to_bv 64 86796) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (R0 : rr = Z_to_bv 64 0) by (apply Hrr; exact X1). subst rr.
    zstep. if_cases HZ.
    + exfalso. vm_compute in HZ. discriminate HZ.
    + zstep. zstep. zstep.
      eapply evt_cut.
      { eapply SC with (sx := x2) (sy := pf_bytes (chain_list r ws)).
        - exact BP2.
        - exact NP2.
        - rewrite unsigned_lit by lia. exact SY2.
        - apply notin_nul_pf, chain_items_nz. }
      intros ms' (rr & y11 & y12 & y13 & E & Hrr2). subst ms'.
      replace (ret_pc (Z_to_bv 64 86812)) with (Z_to_bv 64 86812) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      assert (R2 : rr = Z_to_bv 64 0) by (apply Hrr2; exact X2). subst rr.
      zstep. if_cases HZ2.
      * exfalso. vm_compute in HZ2. discriminate HZ2.
      * do 13 zstep.
        release_frame FRA ST2 (bv_unsigned sp + -889).
        release_frame BUF2 ST2 (bv_unsigned sp + -873).
        release_frame LC ST2 (bv_unsigned sp + -104).
        release_frame FRH ST2 (bv_unsigned sp).
        zstep. zstep.
        finish.
Qed.

Lemma loop : forall n k mc Fc fcc j0 j1 jb jl rac t0c t1c t2c s2c s3c s4c a0c a1c a2c a3c a4c a5c a6c a7c
    t3c t4c t5c t6c,
  n = Z.to_nat (r - k) -> 2 <= k < r ->
  mem_inv rsegs mc -> munch [(lo, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp + -912) -> frm0 fcc ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
  rw_cells rsegs mc (bv_unsigned sp + -912) [CB 8 j0; C8 a0; CB 7 j1] ->
  rw_cells rsegs mc (bv_unsigned sp + -889) [CB 16 jb] ->
  bytes_at rsegs mc (bv_unsigned sp + -873) (pf_bytes (chain_items 2 (Z.to_nat (k - 2)) ws ++ [0]) ++ jl) ->
  wr_at rsegs mc (bv_unsigned sp + -873) 769 ->
  Z.of_nat (length (chain_items 2 (Z.to_nat (k - 2)) ws)) + 1 + Z.of_nat (length jl) = 769 ->
  rw_cells rsegs mc (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs (fp_void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo m)
    (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -912)) gp tp t0c t1c t2c (Z_to_bv 64 k) (Z_to_bv 64 r)
             a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c (Z_to_bv 64 67384)
             (Z_to_bv 64 (Z.of_nat (length (chain_items 2 (Z.to_nat (k - 2)) ws))))
             (Z_to_bv 64 (bv_unsigned a1 + 8 * k)) (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -873))
             (Z_to_bv 64 769) (Z_to_bv 64 67624) t3c t4c t5c t6c)
        Fc (Z_to_bv 64 0x15298) fcc None mc (seg_rom rsegs)).
Proof.
  intros n. induction n as [|n IH];
    intros k mc Fc fcc j0 j1 jb jl rac t0c t1c t2c s2c s3c s4c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c
      HNk Hk MI MU WM ST FRM FP FRA BUF LIST LW LL FRH; [lia|].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold CommandModel.IMG_END in IE.
  pose proof (chain_items_len (Z.to_nat (k - 2)) 2 ws) as HLn.
  remember (chain_items 2 (Z.to_nat (k - 2)) ws) as L eqn:EL.
  assert (HLo : Z.of_nat (length L) <= 12 * (k - 2)) by lia.
  destruct (slot_transport _ _ _ _ _ _ _ (HW k ltac:(lia)) MU) as (SK & BK & NK).
  remember (nth (Z.to_nat k) wp (Z_to_bv 64 0)) as pk eqn:Epk.
  remember (nth (Z.to_nat k) ws []) as wk eqn:Ewk.
  pose proof (bytes_at_bound _ _ _ _ SK) as SKB. rewrite length_le8 in SKB.
  assert (RK : ov_read_bytes rsegs mc (wa (bv_unsigned a1 + 8 * k)) 8 = Some (le8 pk)).
  { replace (wa (bv_unsigned a1 + 8 * k)) with (wa (bv_unsigned a1 + 8 * k + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs mc _ (le8 pk) 0 8 SK ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (BODY : forall fa fmt ps,
    ro_bytes_b rsegs fa (pf_bytes (fmt ++ [0])) = true -> RO_LO <= fa -> fa + Z.of_nat (length fmt) + 1 <= RO_END ->
    pf_parse fmt = Some ps -> (forall v, pf_text ps [AInt v] = Some ((if Nat.eqb (Z.to_nat k) 2 then [] else [32]) ++ pf_dec v)) ->
    evt rsegs (fp_void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo m)
      (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -912)) gp tp t0c t1c t2c (Z_to_bv 64 k) (Z_to_bv 64 r)
               a0c a1c a2c a3c a4c a5c a6c a7c (Z_to_bv 64 fa) s3c s4c (Z_to_bv 64 67384)
               (Z_to_bv 64 (Z.of_nat (length L)))
               (Z_to_bv 64 (bv_unsigned a1 + 8 * k)) (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -873))
               (Z_to_bv 64 769) (Z_to_bv 64 67624) t3c t4c t5c t6c)
          Fc (Z_to_bv 64 0x152a4) fcc None mc (seg_rom rsegs))).
  { intros fa fmt ps HFB RO1 RO2 PP PT.
    unfold RO_LO, RO_END in RO1, RO2.
    zstep. zstep. zstep. zstep.
    rewrite <- (Z_to_bv_bv_unsigned pk).
    eapply evt_cut.
    { eapply ATOI with (A := bv_unsigned pk) (str := wk); [exact BK | exact MI]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                E & MU1 & WM1 & MI1).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 86708)) with (Z_to_bv 64 86708) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    tp_cells MU1 WM1 FRA. tp_cells MU1 WM1 BUF. tp_cells MU1 WM1 FRH.
    tp_bytes MU1 LIST.
    apply (wr_at_transport rsegs mc m1) in LW; [|exact WM1].
    apply (stk_transport_disjoint rsegs [] mc m1 lo _) in ST; [| exact MU1 | exact WM1 | exact I].
    tp_munch MU MU1.
    pose proof (wmono_trans rsegs m mc m1 WM WM1) as WM2.
    clear MU1 WM1 MI WM BK SK RK.
    destruct (guards_at m1 MU WM2) as [G1 G2].
    do 5 zstep.
    remember ((if Nat.eqb (Z.to_nat k) 2 then [] else [32]) ++ pf_dec (atoi_val wk)) as T eqn:ET.
    assert (TL : (length T <= 12)%nat).
    { pose proof (citem_len (Z.to_nat k) ws) as C. unfold citem in C. rewrite <- Ewk, <- ET in C. exact C. }
    pose proof (bytes_at_skipn _ _ _ (length L) LIST ltac:(rewrite length_app, length_pf_bytes, length_app; lia)) as LS.
    rewrite skipn_pf in LS.
    assert (P1 : bytes_at rsegs m1 (bv_unsigned sp + -873) (pf_bytes L)).
    { rewrite pf_bytes_nul, <- app_assoc in LIST. apply bytes_at_app in LIST. exact (proj1 LIST). }
    assert (P3 : bytes_at rsegs m1 (bv_unsigned sp + -873 + Z.of_nat (length L) + 1 + Z.of_nat (length T))
                   (skipn (length T) jl)).
    { change (Z_to_bv 8 0 :: jl) with ([Z_to_bv 8 0] ++ jl) in LS. apply bytes_at_app in LS.
      pose proof (bytes_at_skipn _ _ _ (length T) (proj2 LS) ltac:(lia)) as H3. exact H3. }
    assert (DC : rw_cells rsegs m1 (bv_unsigned sp + -873 + Z.of_nat (length L))
                   [CB (Z.to_nat (769 - Z.of_nat (length L))) (Z_to_bv 8 0 :: jl)]).
    { apply rw_cells_cbn; [exact LS | | cbn [length]; lia].
      rewrite Z2Nat.id by lia. apply (wr_at_sub _ _ 769); [exact LW | lia | lia | lia]. }
    clear LS LIST.
    eapply evt_cut.
    { eapply SNP with (fmt := fmt) (ps := ps) (args := [AInt (atoi_val wk)]) (T := T)
                      (junk := Z_to_bv 8 0 :: jl) (lo := lo) (canary := can).
      - rewrite unsigned_lit by lia. apply lit_at; [exact MI1 | exact HFB | lia |].
        rewrite length_pf_bytes, length_app. cbn [length]. lia.
      - rewrite unsigned_lit by lia. unfold RO_LO. lia.
      - rewrite unsigned_lit by lia. unfold RO_END. lia.
      - exact PP.
      - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [apply atoi_val_range|].
        rewrite unsigned_lit_wrap. apply mod64_32.
      - rewrite ET. apply PT.
      - rewrite !unsigned_lit by lia. exact DC.
      - rewrite unsigned_lit by lia. lia.
      - lia.
      - rewrite !unsigned_lit by lia. lia.
      - right. rewrite !unsigned_lit by lia. lia.
      - apply img_free_hi. rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
      - unfold snprintf_c.IMG_END. lia.
      - rewrite unsigned_lit by lia. lia.
      - exact FRM.
      - exact MI1.
      - exact (TMW m1 MU).
      - exact G1.
      - exact G2. }
    intros ms' PO. unfold printf_post in PO. rewrite !unsigned_lit in PO by lia.
    rewrite firstn_all2 in PO by lia.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                    Ft & fc' & m2 & E & MU2 & WM2' & MI2 & _ & FRM2 & FP2 & ST2 & DB2).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 86728)) with (Z_to_bv 64 86728) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    pose proof (fp_chain Fc Ft FP FP2) as FP3. clear FP FP2.
    tp_cells MU2 WM2' FRA. tp_cells MU2 WM2' BUF. tp_cells MU2 WM2' FRH.
    tp_bytes MU2 P1. tp_bytes MU2 P3.
    apply (wr_at_transport rsegs m1 m2) in LW; [|exact WM2'].
    tp_munch MU MU2.
    pose proof (wmono_trans rsegs m m1 m2 WM2 WM2') as WM3.
    clear MU2 WM2' WM2 MI1 G1 G2 DC ST.
    assert (EL' : chain_items 2 (Z.to_nat (k + 1 - 2)) ws = L ++ T).
    { replace (Z.to_nat (k + 1 - 2)) with (S (Z.to_nat (k - 2))) by lia.
      rewrite chain_items_snoc, <- EL, ET. f_equal. unfold citem.
      replace (2 + Z.to_nat (k - 2))%nat with (Z.to_nat k) by lia. rewrite <- Ewk. reflexivity. }
    assert (LIST2 : bytes_at rsegs m2 (bv_unsigned sp + -873)
                      (pf_bytes (chain_items 2 (Z.to_nat (k + 1 - 2)) ws ++ [0]) ++ skipn (length T) jl)).
    { rewrite EL', pf_bytes_snoc, <- app_assoc.
      eapply bytes_at_app3; [exact P1 | exact DB2 | exact P3 | rewrite length_pf_bytes; reflexivity |].
      rewrite length_pf_bytes, length_app. cbn [length]. lia. }
    assert (LL2 : Z.of_nat (length (chain_items 2 (Z.to_nat (k + 1 - 2)) ws)) + 1 + Z.of_nat (length (skipn (length T) jl)) = 769).
    { rewrite EL', length_app, length_skipn. lia. }
    clear P1 P3 DB2.
    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (Z.of_nat (length L) + Z.of_nat (length T)))
      with (Z_to_bv 64 (Z.of_nat (length (chain_items 2 (Z.to_nat (k + 1 - 2)) ws))))
      by (f_equal; rewrite EL', length_app; lia).
    replace (Z_to_bv 64 (bv_unsigned a1 + 8 * k + 8)) with (Z_to_bv 64 (bv_unsigned a1 + 8 * (k + 1)))
      by (f_equal; lia).
    if_cases HB2.
    - zify_cond HB2.
      eapply (IH (k + 1)); [lia | lia | exact MI2 | exact MU | exact WM3 | exact ST2 | exact FRM2 | exact FP3
                           | exact FRA | exact BUF | exact LIST2 | exact LW | exact LL2 | exact FRH].
    - zify_cond HB2.
      assert (RK1 : r = k + 1) by lia.
      replace (chain_items 2 (Z.to_nat (k + 1 - 2)) ws) with (chain_list r ws) in LIST2, LL2
        by (unfold chain_list; rewrite RK1; reflexivity).
      eapply tail; [exact MI2 | exact MU | exact WM3 | exact ST2 | exact FRM2 | exact FP3
                   | exact FRA | exact BUF | exact LIST2 | exact LW | exact LL2 | exact FRH]. }
  zstep. zstep. if_cases HB.
  - zify_cond HB.
    apply (BODY 67384 [32; 37; 100] [PLit 32; Pd]);
      [vm_compute; reflexivity | unfold RO_LO; lia | unfold RO_END; cbn [length Z.of_nat]; lia | reflexivity |].
    intros v. destruct (Nat.eqb_spec (Z.to_nat k) 2) as [E2|E2]; [lia|].
    cbn [pf_text option_map app]. rewrite app_nil_r. reflexivity.
  - zify_cond HB. zstep.
    apply (BODY 67624 [37; 100] [Pd]);
      [vm_compute; reflexivity | unfold RO_LO; lia | unfold RO_END; cbn [length Z.of_nat]; lia | reflexivity |].
    intros v. destruct (Nat.eqb_spec (Z.to_nat k) 2) as [E2|E2]; [|lia].
    cbn [pf_text option_map app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma entry : forall mc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc,
  a2 = Z_to_bv 64 r -> mem_inv rsegs mc -> munch [(lo, bv_unsigned sp)] m mc -> wmono rsegs m mc ->
  stk rsegs mc lo (bv_unsigned sp) -> frm0 fc ->
  evt rsegs (fp_void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15224) fc None mc (seg_rom rsegs)).
Proof.
  intros mc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc -> MI MU WM ST FRM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold CommandModel.IMG_END in IE.
  assert (SGr : bv_signed (Z_to_bv 64 r) = r).
  { rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec r (2^63)); lia. }
  carve_frame 912%nat ST.
  do 18 zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  apply frame_split in FR. destruct FR as (ja & jb & FRA & BUF & LB & LJ & LW & FRH).
  replace (bv_unsigned sp + -912 + 23) with (bv_unsigned sp + -889) in BUF by lia.
  replace (bv_unsigned sp + -912 + 39) with (bv_unsigned sp + -873) in LB, LW by lia.
  replace (bv_unsigned sp + -912 + 808) with (bv_unsigned sp + -104) in FRH by lia.
  zstep. if_cases HR.
  - zify_cond HR. rewrite SGr in HR.
    assert (CL : chain_list r ws = []).
    { unfold chain_list. replace (Z.to_nat (r - 2)) with 0%nat by lia. reflexivity. }
    eapply tail; [exact MI | exact MU | exact WM | exact ST | exact FRM | intros; reflexivity
                 | exact FRA | exact BUF | rewrite CL; exact LB | exact LW | rewrite CL; cbn [length]; lia | exact FRH].
  - zify_cond HR. rewrite SGr in HR.
    do 10 zstep.
    eapply (loop _ 2); [reflexivity | lia | exact MI | exact MU | exact WM | exact ST | exact FRM | intros; reflexivity
                       | exact FRA | exact BUF | exact LB | exact LW
                       | replace (chain_items 2 (Z.to_nat (2 - 2)) ws) with (@nil Z) by reflexivity; cbn [length]; lia
                       | exact FRH].
Qed.

End Chain.

Theorem check_words_chain_holds : atoi_contract -> snprintf_contract -> strcmp_contract -> check_words_chain_contract.
Proof.
  intros ATOI SNP SC. unfold check_words_chain_contract, CHECK_WORDS_CHAIN, CHECK_WORDS_CHAIN_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros r nargs wp ws p1 p2 x1 x2 can.
  intros MI TM FRM ST LO IE SPH GG GU RR HA2 HW HN HNB HND HP1 HP2 N3 X1 X2.
  subst nargs. specialize (HP1 eq_refl). specialize (HP2 eq_refl).
  pose proof (fun mc => task_mem_munch m mc lo (bv_unsigned sp) TM ST) as TMW.
  eapply entry with (r := r) (wp := wp) (ws := ws) (p1 := p1) (p2 := p2) (x1 := x1) (x2 := x2) (can := can).
  all: first [ eassumption | apply munch_refl | apply wmono_refl ].
Qed.
