(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition mv_cur (off : nat) (bs : list byte) (i : nat) : list byte := firstn i (skipn off bs) ++ skipn i bs.

Lemma mv_cur_0 : forall off bs, mv_cur off bs 0 = bs.
Proof. reflexivity. Qed.

Lemma mv_cur_length : forall off bs i, (off + i <= length bs)%nat -> length (mv_cur off bs i) = length bs.
Proof. intros off bs i H. unfold mv_cur. rewrite length_app, firstn_length, !skipn_length. lia. Qed.

(* [comment removed for export] *)
Lemma mv_cur_skipn : forall off bs i j, (off + i <= length bs)%nat -> (i <= j)%nat -> skipn j (mv_cur off bs i) = skipn j bs.
Proof.
  intros off bs i j H Hj. unfold mv_cur.
  assert (L : length (firstn i (skipn off bs)) = i) by (rewrite firstn_length, skipn_length; lia).
  rewrite skipn_app, L. rewrite (skipn_all2 (firstn i (skipn off bs))) by lia. cbn [app].
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma mv_cur_nth : forall off bs i j, (off + i <= length bs)%nat -> (i <= j)%nat -> nth_error (mv_cur off bs i) j = nth_error bs j.
Proof.
  intros off bs i j H Hj.
  rewrite <- (Nat.add_0_r j) at 1. rewrite <- nth_error_skipn, (mv_cur_skipn off bs i j H Hj), nth_error_skipn, Nat.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mv_cur_upd : forall off bs i k, (off + i + k <= length bs)%nat ->
  upd_bytes (mv_cur off bs i) i (firstn k (skipn (off + i) bs)) = mv_cur off bs (i + k).
Proof.
  intros off bs i k H. unfold upd_bytes.
  assert (Lx : length (firstn k (skipn (off + i) bs)) = k) by (rewrite firstn_length, skipn_length; lia).
  rewrite Lx. rewrite (mv_cur_skipn off bs i (i + k)) by lia.
  unfold mv_cur.
  assert (L : length (firstn i (skipn off bs)) = i) by (rewrite firstn_length, skipn_length; lia).
  rewrite firstn_app, L, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. rewrite firstn_firstn, Nat.min_id.
  rewrite app_assoc. f_equal.
  rewrite firstn_add_split. f_equal. rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a2 : word) (off : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned a0) [CB (length bs) (mv_cur (Z.to_nat off) bs (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (ra sp gp tp t1 t2 s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (off : Z).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation N := (Z.of_nat (length bs)).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis HS : (S = D + off)%Z.
  Hypothesis AB : (0 < off /\ off + n <= N /\ 0 <= D /\ D + N < 2^64 /\ 0 <= n)%Z.

  Notation POST := (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 off bs m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation cur i := (mv_cur (Z.to_nat off) bs (Z.to_nat i)).

  Definition INV (mX : word -> option byte) (i : Z) : Prop :=
    u8arr usegs mX D (cur i) /\ mem_inv usegs mX /\ munch W m mX /\ wmono usegs m mX.

  Ltac open_inv H := destruct H as (DST & MI & MU & WM).

  Lemma cur_len : forall i, (0 <= i <= n)%Z -> length (cur i) = length bs.
  Proof. intros i Hi. apply mv_cur_length. lia. Qed.

  (* [comment removed for export] *)
  Lemma src_byte : forall i, (0 <= i < n)%Z -> exists b, nth_error (cur i) (Z.to_nat (off + i)) = Some b.
  Proof.
    intros i Hi. rewrite mv_cur_nth by lia.
    destruct (nth_error bs (Z.to_nat (off + i))) as [b|] eqn:E; [exists b; reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  Lemma cp_store_ok : forall mX i (k : nat) a,
    INV mX i -> (0 <= i)%Z -> (i + Z.of_nat k <= n)%Z -> a = wa (D + i) -> store_ok usegs mX a k = true.
  Proof.
    intros mX i k a I Hi Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n usegs mX D (cur i) i k a DST); [lia| rewrite cur_len by lia; lia | exact Ha].
  Qed.

  Lemma cp_store : forall mX i xs a,
    INV mX i -> (0 <= i)%Z -> (i + Z.of_nat (length xs) <= n)%Z ->
    firstn (length xs) (skipn (Z.to_nat (off + i)) (cur i)) = xs -> a = wa (D + i) ->
    INV (write_to_mem mX a xs) (i + Z.of_nat (length xs)).
  Proof.
    intros mX i xs a I Hi Hk Hxs Ha. pose proof I as I'. open_inv I.
    pose proof (cp_store_ok mX i (length xs) a I' Hi Hk Ha) as SOK. subst a.
    split; [|split; [|split]].
    - replace (cur (i + Z.of_nat (length xs))) with (upd_bytes (cur i) (Z.to_nat i) xs).
      { apply (u8arr_write_bytes usegs mX D (cur i) i xs DST); [lia|]. rewrite cur_len by lia. lia. }
      rewrite <- Hxs at 1. rewrite (mv_cur_skipn (Z.to_nat off) bs (Z.to_nat i) (Z.to_nat (off + i))) by lia.
      replace (Z.to_nat (off + i)) with (Z.to_nat off + Z.to_nat i)%nat by lia.
      rewrite mv_cur_upd by lia. f_equal. lia.
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma mv_ret : forall mX x5 x11 x12 x13 x14 x15 x16 x17,
    INV mX n -> evt usegs POST (ST 0x2bb3c0 mX x5 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros mX x5 x11 x12 x13 x14 x15 x16 x17 I; open_inv I.
    zstep. apply evt_done. exists x5, t1, t2, x11, x12, x13, x14, x15, x16, x17, t3, t4, t5, t6, mX.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply rw_cells_of_u8arr in DST. rewrite cur_len in DST by lia. exact DST.
  Qed.
  (* [comment removed for export] *)
  Ltac rd1 I i b Hn :=
    lazymatch type of I with INV ?mX _ =>
      let RD := fresh "RD" in
      pose proof (u8arr_read usegs mX D _ (off + i) b (Z_to_bv 64 (S + i)) (proj1 I) Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      zstep; try clear RD
    end.

  (* [comment removed for export] *)
  Ltac st1 I i ADDR b Hn :=
    lazymatch type of I with INV ?mX _ =>
      let SOK := fresh "SOK" in
      pose proof (cp_store_ok mX i 1 (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      zstep; clear SOK;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bytes) _) =>
        replace bytes with [b] by first [reflexivity | symmetry; apply le1_zxb] end;
      let I2 := fresh "I" in
      pose proof (cp_store mX i [b] (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(apply nth_error_first1; exact Hn) ltac:(unfold wa; f_equal; lia)) as I2;
      cbn [length] in I2; change (Z.of_nat 1) with 1%Z in I2;
      let m2 := fresh "m" in
      remember (write_to_mem mX (Z_to_bv 64 ADDR) [b]) as m2 eqn:Em; clear Em;
      clear I; try clear mX; rename I2 into I
    end.

  (* [comment removed for export] *)
  Lemma mv_bytes : forall (K : nat) mX i x5 x11 x15 x16 x17,
    INV mX i -> Z.to_nat (n - i) = K -> (0 <= i < n)%Z ->
    evt usegs POST (ST 0x2bb36c mX x5 x11 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) x15 x16 x17).
  Proof.
    induction K as [|K IH]; intros mX i x5 x11 x15 x16 x17 I HK Hi; [lia|].
    destruct (src_byte i Hi) as [b Hn].
    rd1 I i b Hn.
    do 2 zstep.
    st1 I i (D + i)%Z b Hn.
    do 2 zstep. if_cases Kc; zify_cond Kc.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
      eapply (IH _ (i + 1)%Z); [exact I| lia| lia].
    - zstep. eapply mv_ret. replace n with (i + 1)%Z by lia. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma mv_bentry : forall mX i x5 x11 x15 x16 x17,
    INV mX i -> (0 <= i <= n)%Z ->
    evt usegs POST (ST 0x2bb364 mX x5 x11 (Z_to_bv 64 (n - i)) (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) x15 x16 x17).
  Proof.
    intros mX i x5 x11 x15 x16 x17 I Hi.
    zstep. if_cases K0; zify_cond K0.
    - eapply mv_ret. replace n with i by lia. exact I.
    - zstep. replace (D + i + (n - i))%Z with (D + n)%Z by lia.
      eapply (mv_bytes (Z.to_nat (n - i)) _ i); [exact I| reflexivity| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma mv_words : forall (K : nat) mX i x5 x15 x16 x17,
    INV mX i -> Z.to_nat (n - i) = K -> (0 <= i)%Z -> (i + 8 <= n)%Z ->
    evt usegs POST (ST 0x2bb494 mX x5 (Z_to_bv 64 7) (Z_to_bv 64 (n - i)) (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) x15 x16 x17).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros mX i x5 x15 x16 x17 I HK Hi Hi8.
    pose proof (cur_len i ltac:(lia)) as CLEN.
    pose proof (bytes_at_read usegs mX D (cur i) (off + i) 8 (proj1 (proj1 I)) ltac:(lia) ltac:(rewrite CLEN; lia)) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat (off + i)) (cur i))) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length, CLEN. lia. }
    replace (wa (D + (off + i))) with (Z_to_bv 64 (S + i)) in RD by (unfold wa; f_equal; lia).
    do 2 zstep. clear RD.
    pose proof (cp_store_ok mX i 8 (Z_to_bv 64 (D + i)) I ltac:(lia) ltac:(lia) eq_refl) as SOK.
    zstep. clear SOK.
    rewrite (le8_ld chunk CL).
    pose proof (cp_store mX i chunk (Z_to_bv 64 (D + i)) I ltac:(lia) ltac:(rewrite CL; lia) ltac:(rewrite CL; reflexivity) eq_refl) as I2.
    rewrite CL in I2. change (Z.of_nat 8) with 8%Z in I2.
    remember (write_to_mem mX (Z_to_bv 64 (D + i)) chunk) as m2 eqn:Em; clear Em.
    clear I.
    do 3 zstep. if_cases K8; zify_cond K8.
    - replace (D + i + 8)%Z with (D + (i + 8))%Z by lia. replace (S + i + 8)%Z with (S + (i + 8))%Z by lia.
      replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
      eapply (IH (Z.to_nat (n - (i + 8))) ltac:(lia) _ (i + 8)%Z); [exact I2| reflexivity| lia| lia].
    - zstep.
      replace (D + i + 8)%Z with (D + (i + 8))%Z by lia. replace (S + i + 8)%Z with (S + (i + 8))%Z by lia.
      replace (n - i + -8)%Z with (n - (i + 8))%Z by lia.
      eapply (mv_bentry _ (i + 8)%Z); [exact I2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma mv_wentry : forall mX i x5 x11 x15 x16 x17,
    INV mX i -> (0 <= i <= n)%Z ->
    evt usegs POST (ST 0x2bb488 mX x5 x11 (Z_to_bv 64 (n - i)) (Z_to_bv 64 (D + i)) (Z_to_bv 64 (S + i)) x15 x16 x17).
  Proof.
    intros mX i x5 x11 x15 x16 x17 I Hi.
    do 2 zstep. if_cases K8; zify_cond K8.
    - eapply (mv_bentry _ i); [exact I| lia].
    - zstep. eapply (mv_words (Z.to_nat (n - i)) _ i); [exact I| reflexivity| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma mv_align : forall (K : nat) mX i x5 x13 x14 x17,
    INV mX i -> Z.to_nat (n - i) = K -> (0 <= i <= n)%Z ->
    evt usegs POST (ST 0x2bb3d4 mX x5 (Z_to_bv 64 (S + i)) (Z_to_bv 64 (n - i)) x13 x14 (Z_to_bv 64 (D + i + 1)) (Z_to_bv 64 (D + i)) x17).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros mX i x5 x13 x14 x17 I HK Hi.
    zstep. if_cases K0; zify_cond K0.
    - eapply mv_ret. replace n with i by lia. exact I.
    - destruct (src_byte i ltac:(lia)) as [b Hn].
      zstep.
      rd1 I i b Hn.
      do 3 zstep.
      st1 I i (D + i)%Z b Hn.
      do 4 zstep. if_cases Kal; zify_cond Kal.
      + replace (D + i + 2)%Z with (D + (i + 1) + 1)%Z by lia.
        replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
        replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
        eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) _ (i + 1)%Z); [exact I| reflexivity| lia].
      + zstep.
        replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
        replace (n - i + -1)%Z with (n - (i + 1))%Z by lia.
        eapply (mv_wentry _ (i + 1)%Z); [exact I| lia].
  Qed.
  Lemma bytes_at_sub_ : forall mX A (l : list byte) k j,
    bytes_at usegs mX A l -> (k <= length l)%nat -> bytes_at usegs mX (A + Z.of_nat k) (firstn j (skipn k l)).
  Proof.
    intros mX A l k j H Hk.
    rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite firstn_length, Nat.min_l in H by lia.
    rewrite <- (firstn_skipn j (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma mv_disjoint : forall x5 x13 x14 x15 x16 x17,
    (n <= off)%Z -> rw_cells usegs m D [CB (length bs) bs] -> mem_inv usegs m ->
    evt usegs POST (ST 0x2baf30 m x5 a1 a2 x13 x14 x15 x16 x17).
  Proof.
    intros x5 x13 x14 x15 x16 x17 Hno DST MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (rw_cells_CB_split_at usegs m D (length bs) bs (Z.to_nat n) ltac:(lia) DST) as [DA DB].
    assert (SRC : bytes_at usegs m S (firstn (Z.to_nat n) (skipn (Z.to_nat off) bs))).
    { destruct (u8arr_of_rw_cells usegs m D _ _ DST) as [BA _]. rewrite HS. replace off with (Z.of_nat (Z.to_nat off)) at 1 by lia.
      apply bytes_at_sub_; [exact BA| lia]. }
    clear DST.
    call (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (firstn (Z.to_nat n) (skipn (Z.to_nat off) bs)) (firstn (Z.to_nat n) bs)).
    1:{ exact SRC. } 1:{ rewrite firstn_length, skipn_length. lia. } 1:{ exact DA. } 1:{ right. lia. } 1:{ exact MI. }
    pose proof (rw_cells_CB_join usegs _ D _ _ _ _ PC DB) as J.
    replace (Z.to_nat n + (length bs - Z.to_nat n))%nat with (length bs) in J by lia.
    apply evt_done. unfold memmove_post. do 15 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. exact J.
  Qed.

  (* [comment removed for export] *)
  Lemma memmove_body : forall x5 x13 x14 x15 x16 x17,
    (D + N < 2^63)%Z -> rw_cells usegs m D [CB (length bs) bs] -> mem_inv usegs m ->
    evt usegs POST (ST 0x2bb334 m x5 a1 a2 x13 x14 x15 x16 x17).
  Proof.
    intros x5 x13 x14 x15 x16 x17 H63 DST MI.
    zstep. if_cases Ke; zify_cond Ke. { exfalso. lia. }
    do 5 zstep. if_cases Kd; zify_cond Kd.
    - zstep. eapply mv_disjoint; [|exact DST|exact MI].
      destruct (Z_le_gt_dec n off) as [|G]; [assumption|]. exfalso.
      rewrite Z.shiftl_mul_pow2 in Kd by lia. change (2 ^ 1)%Z with 2%Z in Kd.
      revert Kd. Z.div_mod_to_equations. lia.
    - assert (I : INV m 0).
      { split; [exact (u8arr_of_rw_cells usegs m D _ _ DST)|]. split; [exact MI|]. split; [apply munch_refl | apply wmono_refl]. }
      clear DST MI.
      do 3 zstep. if_cases Kb; zify_cond Kb. { exfalso. lia. }
      zstep. if_cases Kx.
      + (* [comment removed for export] *)
        do 2 zstep. if_cases Kal.
        * do 2 zstep.
          eapply evt_eq.
          2:{ eapply (mv_wentry _ 0 _ _ _ _ _); [exact I| lia]. }
          unfold mkR. rewrite !Z.add_0_r, !Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
        * do 2 zstep.
          eapply evt_eq.
          2:{ eapply (mv_align (Z.to_nat n) _ 0 _ _ _ _); [exact I| f_equal; lia| lia]. }
          unfold mkR. rewrite !Z.add_0_r, !Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
      + do 2 zstep.
        eapply evt_eq.
        2:{ eapply (mv_bentry _ 0 _ _ _ _ _); [exact I| lia]. }
        unfold mkR. rewrite !Z.add_0_r, !Z.sub_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.

Lemma mv_cur_off0 : forall bs k, mv_cur 0 bs k = bs.
Proof. intros bs k. unfold mv_cur. cbn [skipn]. apply firstn_skipn. Qed.

(* [comment removed for export] *)
Definition memmove_fwd_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bs : list byte) (off : Z),
  rw_cells usegs m (bv_unsigned a0) [CB (length bs) bs] ->
  (bv_unsigned a1 = bv_unsigned a0 + off)%Z -> (0 <= off)%Z -> (off + bv_unsigned a2 <= Z.of_nat (length bs))%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) < 2^63)%Z ->
  mem_inv usegs m ->
  evt usegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 off bs m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2bb334) fc None m (seg_rom usegs)).

Theorem memmove_fwd_proof : memmove_fwd_stmt.
Proof.
  unfold memmove_fwd_stmt. intros until off. intros DST HS Hoff Hn H63 MI.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  destruct (Z.eq_dec off 0) as [E0|N0].
  - (* [comment removed for export] *)
    assert (Ea : a1 = a0) by (apply bv_eq; lia). subst a1 off.
    zstep. if_true. zstep.
    apply evt_done. unfold memmove_post. do 14 eexists. exists m.
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    change (Z.to_nat 0) with 0%nat. rewrite mv_cur_off0. exact DST.
  - eapply memmove_body; try eassumption; lia.
Qed.
