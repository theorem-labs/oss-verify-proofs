(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memset F_memmove.
Import ListNotations.
Open Scope bv_scope.

Definition stpncpy_entry := 0x24a88%Z.
Definition strncpy_entry := 0x24a60%Z.

Section ListFacts.
  Open Scope Z_scope.

  Definition stpn_k (str : list byte) (n : nat) : nat := Nat.min (length str) n.
  Definition stpn_result (str : list byte) (n : nat) : list byte :=
    firstn (stpn_k str n) str ++ repeat (Z_to_bv 8 0) (n - stpn_k str n).

  #[using="Type"] Lemma stpn_result_length : forall str n, length (stpn_result str n) = n.
  Proof. intros. unfold stpn_result, stpn_k. rewrite app_length, firstn_length, repeat_length. lia. Qed.

  #[using="Type"] Lemma upd_bytes_at_prefix : forall (pre rest xs : list byte),
    (length xs <= length rest)%nat ->
    upd_bytes (pre ++ rest) (length pre) xs = pre ++ xs ++ skipn (length xs) rest.
  Proof.
    intros pre rest xs H. unfold upd_bytes. rewrite firstn_app, firstn_all, Nat.sub_diag by lia. cbn.
    rewrite app_nil_r. rewrite skipn_app. replace (length pre + length xs - length pre)%nat with (length xs) by lia.
    rewrite (skipn_all2 pre) by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma firstn_slice_succ : forall (str : list byte) i b, nth_error str i = Some b ->
    firstn i str ++ [b] = firstn (i + 1) str.
  Proof. intros. rewrite Nat.add_1_r. symmetry. apply firstn_S_nth. assumption. Qed.

  #[using="Type"] Lemma slice_app_l : forall (a b : list byte) i k, (i + k <= length a)%nat -> slice (a ++ b) i k = slice a i k.
  Proof.
    intros a b i k H. unfold slice. rewrite skipn_app. replace (i - length a)%nat with 0%nat by lia. cbn [skipn].
    rewrite firstn_app. replace (k - length (skipn i a))%nat with 0%nat by (rewrite skipn_length; lia). cbn [firstn].
    apply app_nil_r.
  Qed.

  #[using="Type"] Lemma firstn_app_slice : forall (str : list byte) i k, (i + k <= length str)%nat ->
    firstn i str ++ slice str i k = firstn (i + k) str.
  Proof.
    intros str i k H. change (firstn i str) with (slice str 0 i). change (firstn (i + k) str) with (slice str 0 (i + k)).
    change (slice str i k) with (slice str (0 + i) k). apply slice_app. lia.
  Qed.
End ListFacts.

Section ArrFacts.
  Open Scope Z_scope.

  #[using="Type"] Lemma u8arr_app_inv : forall m A xs ys, u8arr rsegs m A (xs ++ ys) ->
    u8arr rsegs m A xs /\ u8arr rsegs m (A + Z.of_nat (length xs)) ys.
  Proof.
    intros m A xs ys [Hb Hw]. apply bytes_at_app in Hb. destruct Hb as [H1 H2].
    destruct Hw as (HA & HL & Hw). rewrite app_length in HL. split; split; try assumption.
    - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. rewrite app_length. lia.
    - split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (length xs) + i) with (A + (Z.of_nat (length xs) + i)) by lia. apply Hw. rewrite app_length. lia.
  Qed.

  #[using="Type"] Lemma u8arr_app : forall m A xs ys, u8arr rsegs m A xs -> u8arr rsegs m (A + Z.of_nat (length xs)) ys ->
    u8arr rsegs m A (xs ++ ys).
  Proof.
    intros m A xs ys [H1 W1] [H2 W2]. split. { apply bytes_at_app. split; assumption. }
    destruct W1 as (HA & HL & W1). destruct W2 as (HA2 & HL2 & W2). rewrite app_length. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (length xs))).
    - apply W1. lia.
    - replace (A + i) with (A + Z.of_nat (length xs) + (i - Z.of_nat (length xs))) by lia. apply W2. lia.
  Qed.
End ArrFacts.

Definition stpncpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (stpn_k str (Z.to_nat (bv_unsigned a2)))))
                 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ u8arr rsegs m' (bv_unsigned a0) (stpn_result str (Z.to_nat (bv_unsigned a2)))
    /\ bytes_at rsegs m' (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation SP := (bv_unsigned sp).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 16, bv_unsigned sp)]%Z.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + len + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis SEP : (D + n <= S \/ S + len + 1 + Z.of_nat (length slack) <= D)%Z.
  Hypothesis SEPD : (D + n <= lo \/ SP <= D)%Z.
  Hypothesis SEPS : (S + len + 1 + Z.of_nat (length slack) <= SP - 16 \/ SP <= S)%Z.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis BND : (0 <= D /\ D + n < 2^64 /\ 0 <= S /\ S + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= lo /\ SP < 2^64 /\ 0 <= n)%Z.

  Definition nn := Z.to_nat n.
  Notation POST := (stpncpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 str slack lo m).

  Notation ST pc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x8 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).
  Notation CMAGIC := 72340172838076672%Z.
  Notation HIGHS := 9259542123273814144%Z.

  Definition INV (m1 : word -> option byte) (i : nat) (rest : list byte) : Prop :=
    u8arr rsegs m1 D (firstn i str ++ rest) /\ length rest = (nn - i)%nat /\ (i <= length str)%nat /\ (i <= nn)%nat /\
    bytes_at rsegs m1 S full /\ mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1 /\
    stk rsegs m1 lo (SP - 16) /\ rw_cells rsegs m1 (SP + -16) [C8 s0; C8 ra].

  Ltac open_inv H := destruct H as (DST & LR & IL & IN & SRC & MI & MU & WM & STK & FR).
  Ltac pg := match goal with |- ?G => idtac G end.

  #[using="SEP SEPD SEPS LO BND"] Lemma bounds : (Z.of_nat nn = n /\ 0 <= D /\ D + n < 2^64 /\ 0 <= S /\ S + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= lo /\ SP < 2^64)%Z.
  Proof. unfold nn. lia. Qed.

  #[using="a1"] Lemma full_length : length full = (length str + Datatypes.S (length slack))%nat.
  Proof. rewrite app_length. cbn. lia. Qed.

  #[using="a1 NONUL"] Lemma full_nth_lt : forall i, (i < length str)%nat -> exists b, nth_error full i = Some b /\ nth_error str i = Some b /\ bv_unsigned b <> 0%Z.
  Proof.
    intros i Hi. destruct (nth_error str i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    exists b. split. { rewrite nth_error_app1 by lia. exact E. } split; [reflexivity|].
    intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hb. reflexivity.
  Qed.

  #[using="a1"] Lemma full_nth_len : nth_error full (length str) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

  #[using="a1 slack"] Lemma prefix_length : forall i rest, (i <= length str)%nat -> length (firstn i str ++ rest) = (i + length rest)%nat.
  Proof. intros. rewrite app_length, firstn_length_le by lia. reflexivity. Qed.

  #[using="PAD SEP SEPD SEPS LO BND"] Lemma sp_store : forall m1 i rest xs a,
    INV m1 i rest -> (length xs <= length rest)%nat -> a = wa (D + Z.of_nat i) ->
    store_ok rsegs m1 a (length xs) = true /\
    (u8arr rsegs (write_to_mem m1 a xs) D (firstn i str ++ xs ++ skipn (length xs) rest) /\
     bytes_at rsegs (write_to_mem m1 a xs) S full /\ mem_inv rsegs (write_to_mem m1 a xs) /\
     munch W m (write_to_mem m1 a xs) /\ wmono rsegs m (write_to_mem m1 a xs) /\
     stk rsegs (write_to_mem m1 a xs) lo (SP - 16) /\ rw_cells rsegs (write_to_mem m1 a xs) (SP + -16) [C8 s0; C8 ra]).
  Proof.
    intros m1 i rest xs a I Hl Ha; open_inv I. pose proof bounds as B.
    pose proof (prefix_length i rest IL) as PL.
    assert (SOK : store_ok rsegs m1 a (length xs) = true).
    { eapply (u8arr_store_ok_n rsegs m1 D _ (Z.of_nat i) (length xs) a DST); [lia| rewrite PL; lia | rewrite Ha; reflexivity]. }
    split; [exact SOK|]. subst a. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - pose proof (u8arr_write_bytes rsegs m1 D _ (Z.of_nat i) xs DST ltac:(lia) ltac:(rewrite Nat2Z.id, PL; lia)) as U.
      rewrite Nat2Z.id in U. replace i with (length (firstn i str)) in U at 3 by (rewrite firstn_length_le; lia).
      rewrite upd_bytes_at_prefix in U by lia. exact U.
    - apply bytes_at_write_other; [exact SRC| lia| lia|]. rewrite full_length. lia.
    - apply mem_inv_store; [exact MI| exact SOK].
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
    - apply stk_write; [exact STK| lia| lia].
    - apply rw_cells_frame; [exact FR| lia| lia|]. cbn [cells_size csize Nat.add]. lia.
  Qed.

  Ltac spst_fin I2 xs bytes_tac :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      replace bs0 with xs by bytes_tac;
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : u8arr _ m1 _ _ |- _ => clear H
      | H : bytes_at _ m1 _ _ |- _ => clear H
      | H : mem_inv _ m1 |- _ => clear H
      | H : munch _ _ m1 |- _ => clear H
      | H : wmono _ _ m1 |- _ => clear H
      | H : stk _ m1 _ _ |- _ => clear H
      | H : rw_cells _ m1 _ _ |- _ => clear H
      | H : INV m1 _ _ |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a xs) as m' eqn:E; clear E; try clear m1;
      destruct I2 as (DST & SRC & MI & MU & WM & STK & FR)
    end.
  Ltac by_byte := symmetry; apply le1_zxb.

  Ltac spst_name xs bytes_tac :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      replace bs0 with xs by bytes_tac;
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : u8arr _ m1 _ _ |- _ => clear H
      | H : bytes_at _ m1 _ _ |- _ => clear H
      | H : mem_inv _ m1 |- _ => clear H
      | H : munch _ _ m1 |- _ => clear H
      | H : wmono _ _ m1 |- _ => clear H
      | H : stk _ m1 _ _ |- _ => clear H
      | H : rw_cells _ m1 _ _ |- _ => clear H
      | H : INV m1 _ _ |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a xs) as m' eqn:E; clear E; try clear m1
    end.

  #[using="PAD SEP SEPD SEPS LO BND"] Lemma sp_tail : forall m1 i rest x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31,
    INV m1 i rest -> (i = length str \/ i = nn)%nat ->
    evt rsegs POST (ST 0x24b6c m1 x1 x5 x6 x7 x10 x11 x12 (Z_to_bv 64 (n - Z.of_nat i)) x14 x15 x16 x17 (Z_to_bv 64 (D + Z.of_nat i)) x28 x29 x30 x31).
  Proof.
    intros m1 i rest x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31 I Hi; pose proof I as I'; open_inv I'. pose proof bounds as B.
    pose proof (prefix_length i rest IL) as PL.

    destruct (u8arr_app_inv m1 D (firstn i str) rest DST) as [DST1 DST2].
    rewrite firstn_length_le in DST2 by lia.
    pose proof (rw_cells_of_u8arr rsegs m1 _ _ DST2) as DST3. rewrite LR in DST3. clear DST DST2.
    zstep. zstep. zstep. zstep.
    pose proof (unsigned_lit (D + Z.of_nat i) ltac:(lia)) as U1. pose proof (unsigned_lit (n - Z.of_nat i) ltac:(lia)) as U2.
    pose proof (firstn_length_le str IL) as FL.
    call memset_spec.
    1:{ rewrite U1, U2. replace (Z.to_nat (n - Z.of_nat i)) with (nn - i)%nat by lia. exact DST3. }
    1:{ exact MI. }
    rewrite U1, U2 in POST. change ((bv_unsigned (Z_to_bv 64 0)) mod 256)%Z with 0%Z in POST.
    replace (Z.to_nat (n - Z.of_nat i)) with (nn - i)%nat in POST by lia.
    apply u8arr_of_rw_cells in POST.
    rewrite <- FL in POST at 1. pose proof (u8arr_app _ D (firstn i str) _ DST1 POST) as DST. clear DST1 POST.
    assert (Ei : i = stpn_k str nn) by (unfold stpn_k; lia).
    replace (firstn i str ++ repeat (Z_to_bv 8 0) (nn - i)) with (stpn_result str nn) in DST by (unfold stpn_result; rewrite <- Ei; reflexivity).
    do 5 zstep. rewrite Ei. release_frame FR STK (bv_unsigned sp). finish.
  Qed.

  #[using="sp a0 a1 a2 lo NONUL SEP SEPD SEPS LO BND"] Lemma src_byte : forall i, (i <= length str)%nat ->
    exists b, nth_error full i = Some b /\ (bv_unsigned b = 0%Z <-> i = length str) /\
              ((i < length str)%nat -> nth_error str i = Some b).
  Proof.
    intros i Hi. destruct (Nat.eq_dec i (length str)) as [->|NE].
    - exists (Z_to_bv 8 0). split; [apply full_nth_len|]. split; [split; intros; reflexivity| intros; lia].
    - destruct (full_nth_lt i ltac:(lia)) as (b & H1 & H2 & H3). exists b. split; [exact H1|]. split; [| intros; exact H2].
      split; intros; [exfalso; exact (H3 H)| lia].
  Qed.

  Ltac reg_eq := first [ reflexivity | f_equal; lia | etransitivity; [symmetry; apply Z_to_bv_bv_unsigned|]; f_equal; lia ].

  #[using="PAD SEP SEPD SEPS LO BND"] Lemma sp_tail' : forall m1 i rest x1 x5 x6 x7 x10 x11 x12 xa3 x14 x15 x16 x17 xs0 x28 x29 x30 x31,
    INV m1 i rest -> (i = length str \/ i = nn)%nat ->
    xa3 = Z_to_bv 64 (n - Z.of_nat i) -> xs0 = Z_to_bv 64 (D + Z.of_nat i) ->
    evt rsegs POST (ST 0x24b6c m1 x1 x5 x6 x7 x10 x11 x12 xa3 x14 x15 x16 x17 xs0 x28 x29 x30 x31).
  Proof. intros; subst; eapply sp_tail; eauto. Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma byte_step : forall m1 i rest b,
    INV m1 i rest -> (i < nn)%nat -> nth_error full i = Some b -> (bv_unsigned b = 0%Z <-> i = length str) ->
    store_ok rsegs m1 (Z_to_bv 64 (D + Z.of_nat i)) 1 = true /\
    (bv_unsigned b <> 0%Z -> INV (write_to_mem m1 (Z_to_bv 64 (D + Z.of_nat i)) [b]) (i + 1) (skipn 1 rest)) /\
    (bv_unsigned b = 0%Z -> INV (write_to_mem m1 (Z_to_bv 64 (D + Z.of_nat i)) [b]) i (b :: skipn 1 rest)).
  Proof.
    intros m1 i rest b I Hi Hb Hz. pose proof I as I'; open_inv I'. pose proof bounds as B.
    destruct (sp_store m1 i rest [b] (Z_to_bv 64 (D + Z.of_nat i)) I ltac:(cbn; lia) ltac:(unfold wa; reflexivity))
      as (SOK & DST' & SRC' & MI' & MU' & WM' & STK' & FR').
    cbn [length] in SOK, DST'. split; [exact SOK|]. split; intros Hbz.
    - assert (Hil : (i < length str)%nat) by (destruct (Nat.eq_dec i (length str)); [exfalso; apply Hbz, Hz; assumption| lia]).
      split; [| split; [| split; [lia| split; [lia| split; [exact SRC'| split; [exact MI'| split; [exact MU'| split; [exact WM'| split; [exact STK'| exact FR']]]]]]]]].
      + change (b :: skipn 1 rest) with ([b] ++ skipn 1 rest) in DST'. rewrite app_assoc in DST'.
        rewrite (firstn_slice_succ str i b) in DST'; [exact DST'|].
        destruct (full_nth_lt i Hil) as (b' & E1 & E2 & _). rewrite Hb in E1. injection E1 as <-. exact E2.
      + rewrite skipn_length. lia.
    - apply Hz in Hbz. subst i. split; [exact DST'|]. split; [cbn [length]; rewrite skipn_length; lia|]. split; [lia|]. split; [lia|].
      split; [exact SRC'| split; [exact MI'| split; [exact MU'| split; [exact WM'| split; [exact STK'| exact FR']]]]].
  Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_bytes : forall (r : nat) (i : nat) m1 rest x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x28 x29 x30 x31,
    (r = nn - i)%nat -> (i < nn)%nat -> INV m1 i rest ->
    evt rsegs POST (ST 0x24aac m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (S + Z.of_nat i)) x12 (Z_to_bv 64 (n - Z.of_nat i)) x14 x15 x16 x17
                       (Z_to_bv 64 (D + Z.of_nat i)) x28 x29 x30 x31).
  Proof.
    induction r as [|r IH]; intros i m1 rest x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x28 x29 x30 x31 Hr Hi I; [lia|].
    pose proof I as I'; open_inv I'. pose proof bounds as B.
    destruct (src_byte i IL) as (b & Hb & Hz & Hstr). pose proof (byte_range b).
    pose proof (u8ro_read rsegs m1 S full (Z.of_nat i) b (Z_to_bv 64 (S + Z.of_nat i)) SRC ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD.
    destruct (byte_step m1 i rest b I Hi Hb Hz) as (SOK & In0 & Iz).
    zstep. zstep. spst_name [b] by_byte.
    zstep. if_cases Kz; zify_cond Kz.
    -
      pose proof (Iz Kz) as I2. apply Hz in Kz.
      eapply (sp_tail' _ i); [exact I2| lia| reg_eq| reg_eq].
    - pose proof (In0 Kz) as I2.
      zstep. zstep. zstep. zstep. if_cases Kr; zify_cond Kr.
      + replace (S + Z.of_nat i + 1)%Z with (S + Z.of_nat (i + 1))%Z by lia.
        replace (D + Z.of_nat i + 1)%Z with (D + Z.of_nat (i + 1))%Z by lia.
        replace (n - Z.of_nat i + -1)%Z with (n - Z.of_nat (i + 1))%Z by lia.
        apply (IH (i + 1)%nat _ (skipn 1 rest)); try lia. exact I2.
      + zstep. eapply (sp_tail' _ (i + 1)%nat); [exact I2| lia| reg_eq| reg_eq].
  Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_bentry : forall (i : nat) m1 rest x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    (i <= nn)%nat -> INV m1 i rest ->
    evt rsegs POST (ST 0x24aa4 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (S + Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i)) x13 x14 x15 x16 x17
                       (Z_to_bv 64 (D + Z.of_nat i)) x28 x29 x30 x31).
  Proof.
    intros i m1 rest x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hi I. pose proof bounds as B.
    zstep. if_cases K0; zify_cond K0.
    - zstep. eapply (sp_tail' _ i); [exact I| lia| reg_eq| reg_eq].
    - zstep. apply (sp_bytes (nn - i) i _ rest); try lia. exact I.
  Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_bentry' : forall (i : nat) m1 rest x1 x5 x6 x7 x10 xa1 xa2 x13 x14 x15 x16 x17 xs0 x28 x29 x30 x31,
    (i <= nn)%nat -> INV m1 i rest ->
    xa1 = Z_to_bv 64 (S + Z.of_nat i) -> xa2 = Z_to_bv 64 (n - Z.of_nat i) -> xs0 = Z_to_bv 64 (D + Z.of_nat i) ->
    evt rsegs POST (ST 0x24aa4 m1 x1 x5 x6 x7 x10 xa1 xa2 x13 x14 x15 x16 x17 xs0 x28 x29 x30 x31).
  Proof. intros; subst; eapply sp_bentry; eauto. Qed.

  #[using="a1 str slack"] Lemma b2z_word_zero_iff : forall t, bv_unsigned (Z_to_bv 64 (Z.b2z t)) = 0%Z <-> t = false.
  Proof. intros t. rewrite unsigned_lit by (destruct t; cbn; lia). destruct t; cbn; split; intros; first [congruence | lia]. Qed.

  #[using="sp a0 a2 lo PAD SEP SEPD SEPS LO BND"] Lemma src_word : forall i, (i <= length str)%nat -> ((S + Z.of_nat i) mod 8 = 0)%Z -> (i + 8 <= length full)%nat.
  Proof. intros i Hi Hal. rewrite full_length. pose proof bounds. Z.div_mod_to_equations. lia. Qed.

  #[using="PAD SEP SEPD SEPS LO BND"] Lemma word_step : forall m1 i rest (ch : list byte),
    INV m1 i rest -> (i + 8 <= nn)%nat -> (i + 8 <= length str)%nat -> ch = slice full i 8 ->
    store_ok rsegs m1 (Z_to_bv 64 (D + Z.of_nat i)) 8 = true /\
    INV (write_to_mem m1 (Z_to_bv 64 (D + Z.of_nat i)) ch) (i + 8) (skipn 8 rest).
  Proof.
    intros m1 i rest ch I Hi Hl ->. pose proof I as I'; open_inv I'. pose proof bounds as B.
    assert (CL : length (slice full i 8) = 8%nat) by (apply slice_length; rewrite full_length; lia).
    destruct (sp_store m1 i rest (slice full i 8) (Z_to_bv 64 (D + Z.of_nat i)) I ltac:(rewrite CL; lia) ltac:(unfold wa; reflexivity))
      as (SOK & DST' & SRC' & MI' & MU' & WM' & STK' & FR').
    rewrite CL in SOK, DST'. split; [exact SOK|].
    split; [| split; [rewrite skipn_length; lia| split; [lia| split; [lia| split; [exact SRC'| split; [exact MI'| split; [exact MU'| split; [exact WM'| split; [exact STK'| exact FR']]]]]]]]].
    replace (firstn i str ++ slice full i 8 ++ skipn 8 rest) with ((firstn i str ++ slice str i 8) ++ skipn 8 rest) in DST'.
    2:{ rewrite <- app_assoc. rewrite (slice_app_l str _ i 8) by lia. reflexivity. }
    rewrite firstn_app_slice in DST' by lia. exact DST'.
  Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_words : forall (r : nat) (i : nat) m1 rest x1 x5 x6 x7 x10 x16 x17 x28 x29 x30 x31,
    (r = nn - i)%nat -> (i + 8 <= nn)%nat -> ((S + Z.of_nat i) mod 8 = 0)%Z -> INV m1 i rest ->
    evt rsegs POST (ST 0x24b3c m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (S + Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) (Z_to_bv 64 7) x16 x17
                       (Z_to_bv 64 (D + Z.of_nat i)) x28 x29 x30 x31).
  Proof.
    induction r as [r IH] using lt_wf_ind; intros i m1 rest x1 x5 x6 x7 x10 x16 x17 x28 x29 x30 x31 Hr Hi Hal I; subst r.
    pose proof I as I'; open_inv I'. pose proof bounds as B.
    pose proof (src_word i IL Hal) as HW.
    pose proof (bytes_at_read rsegs m1 S full (Z.of_nat i) 8 SRC ltac:(lia) ltac:(rewrite Nat2Z.id; exact HW)) as RD.
    rewrite Nat2Z.id in RD. change (firstn 8 (skipn i full)) with (slice full i 8) in RD.
    set (ch := slice full i 8) in RD.
    assert (CL : length ch = 8%nat) by (subst ch; apply slice_length; lia).
    pose proof (le_val_range _ (bytes_ok_map ch)) as WR. rewrite length_map, CL in WR. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    zstep. zstep. zstep. zstep. rewrite (load8_le_val ch CL). zstep. if_cases K; zify_cond K.
    -
      zstep. apply (sp_bytes (nn - i) i _ rest); try lia. exact I.
    - apply (haszero64_clang _ (bytes_ok_map ch) ltac:(rewrite length_map; exact CL)) in K. rewrite In0_map_unsigned in K.
      assert (Hi8 : (i + 8 <= length str)%nat).
      { destruct (Nat.lt_ge_cases (length str) (i + 8)); [|assumption]. exfalso. apply K. subst ch.
        unfold slice. apply nth_error_In with (n := (length str - i)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      destruct (word_step m1 i rest ch I Hi Hi8 eq_refl) as [SOK I2].
      zstep. spst_name ch ltac:(symmetry; apply le8_of_load8; exact CL).
      zstep. zstep. zstep. zstep. if_cases K8; zify_cond K8.
      + replace (S + Z.of_nat i + 8)%Z with (S + Z.of_nat (i + 8))%Z by lia.
        replace (D + Z.of_nat i + 8)%Z with (D + Z.of_nat (i + 8))%Z by lia.
        replace (n - Z.of_nat i + -8)%Z with (n - Z.of_nat (i + 8))%Z by lia.
        apply (IH (nn - (i + 8))%nat ltac:(lia) (i + 8)%nat _ (skipn 8 rest)); first [exact I2 | lia | Z.div_mod_to_equations; lia].
      + zstep. eapply (sp_bentry' (i + 8)%nat); [| exact I2| reg_eq| reg_eq| reg_eq]. lia.
  Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_mid : forall (i : nat) m1 rest (fl : word) x1 x5 x6 x7 x10 x13 x15 x16 x17 x28 x29 x30 x31,
    (i <= nn)%nat -> INV m1 i rest -> (bv_unsigned fl = 0%Z <-> i = nn) ->
    (bv_unsigned fl <> 0%Z -> ((S + Z.of_nat i) mod 8 = 0)%Z) ->
    evt rsegs POST (ST 0x24b14 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (S + Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i)) x13 fl x15 x16 x17
                       (Z_to_bv 64 (D + Z.of_nat i)) x28 x29 x30 x31).
  Proof.
    intros i m1 rest fl x1 x5 x6 x7 x10 x13 x15 x16 x17 x28 x29 x30 x31 Hi I Hfl Hal. pose proof I as I'; open_inv I'. pose proof bounds as B.
    zstep. if_cases K0; zify_cond K0.
    -   apply Hfl in K0. zstep. eapply (sp_tail' _ i); [exact I| lia| reg_eq| reg_eq].
    - assert (Hin : (i < nn)%nat) by (destruct (Nat.eq_dec i nn); [exfalso; apply K0, Hfl; assumption| lia]).
      specialize (Hal K0).
      destruct (src_byte i IL) as (b & Hb & Hz & Hstr). pose proof (byte_range b).
      pose proof (u8ro_read rsegs m1 S full (Z.of_nat i) b (Z_to_bv 64 (S + Z.of_nat i)) SRC ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases Kz; zify_cond Kz.
      +   apply Hz in Kz. zstep. zstep. eapply (sp_tail' _ i); [exact I| lia| reg_eq| reg_eq].
      + zstep. zstep. if_cases K8; zify_cond K8.
        * apply (sp_bentry i _ rest); [lia| exact I].
        * zstep. zstep. zstep. zstep. zstep.
          apply (sp_words (nn - i) i _ rest); try lia; try exact I.
  Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_mid' : forall (i : nat) m1 rest (fl : word) x1 x5 x6 x7 x10 xa1 xa2 x13 x15 x16 x17 xs0 x28 x29 x30 x31,
    (i <= nn)%nat -> INV m1 i rest -> (bv_unsigned fl = 0%Z <-> i = nn) ->
    (bv_unsigned fl <> 0%Z -> ((S + Z.of_nat i) mod 8 = 0)%Z) ->
    xa1 = Z_to_bv 64 (S + Z.of_nat i) -> xa2 = Z_to_bv 64 (n - Z.of_nat i) -> xs0 = Z_to_bv 64 (D + Z.of_nat i) ->
    evt rsegs POST (ST 0x24b14 m1 x1 x5 x6 x7 x10 xa1 xa2 x13 fl x15 x16 x17 xs0 x28 x29 x30 x31).
  Proof. intros; subst; eapply sp_mid; eauto. Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_head : forall (r : nat) (i : nat) m1 rest x1 x5 x6 x7 x10 x13 x14 x17 x28 x29 x30 x31,
    (r = nn - i)%nat -> (i < nn)%nat -> INV m1 i rest ->
    evt rsegs POST (ST 0x24ae4 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (S + Z.of_nat i)) (Z_to_bv 64 (n - Z.of_nat i)) x13 x14
                       (Z_to_bv 64 (S + Z.of_nat i + 1)) (Z_to_bv 64 1) x17 (Z_to_bv 64 (D + Z.of_nat i)) x28 x29 x30 x31).
  Proof.
    induction r as [|r IH]; intros i m1 rest x1 x5 x6 x7 x10 x13 x14 x17 x28 x29 x30 x31 Hr Hi I; [lia|].
    pose proof I as I'; open_inv I'. pose proof bounds as B.
    destruct (src_byte i IL) as (b & Hb & Hz & Hstr). pose proof (byte_range b).
    pose proof (u8ro_read rsegs m1 S full (Z.of_nat i) b (Z_to_bv 64 (S + Z.of_nat i)) SRC ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD.
    destruct (byte_step m1 i rest b I Hi Hb Hz) as (SOK & In0 & Iz).
    zstep. zstep. zstep. spst_name [b] by_byte.
    zstep. if_cases Kz; zify_cond Kz.
    - pose proof (Iz Kz) as I2. apply Hz in Kz. eapply (sp_tail' _ i); [exact I2| lia| reg_eq| reg_eq].
    - pose proof (In0 Kz) as I2.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      +
        eapply (sp_mid' (i + 1)%nat _ (skipn 1 rest)); [lia| exact I2| | | reg_eq| reg_eq| reg_eq].
        * rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
        * intros _. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations. lia.
      + zstep. zstep. if_cases K1; zify_cond K1.
        * replace (S + Z.of_nat i + 1)%Z with (S + Z.of_nat (i + 1))%Z by lia.
          replace (S + Z.of_nat i + 2)%Z with (S + Z.of_nat (i + 1) + 1)%Z by lia.
          replace (D + Z.of_nat i + 1)%Z with (D + Z.of_nat (i + 1))%Z by lia.
          replace (n - Z.of_nat i + -1)%Z with (n - Z.of_nat (i + 1))%Z by lia.
          apply (IH (i + 1)%nat _ (skipn 1 rest)); try lia. exact I2.
        * eapply (sp_mid' (i + 1)%nat _ (skipn 1 rest)); [lia| exact I2| | | reg_eq| reg_eq| reg_eq].
          -- rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          -- rewrite b2z_word_zero_iff, Z.ltb_ge. intros. exfalso. lia.
  Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_head' : forall (i : nat) m1 rest x1 x5 x6 x7 x10 xa1 xa2 x13 x14 xa5 xa6 x17 xs0 x28 x29 x30 x31,
    (i < nn)%nat -> INV m1 i rest ->
    xa1 = Z_to_bv 64 (S + Z.of_nat i) -> xa2 = Z_to_bv 64 (n - Z.of_nat i) -> xa5 = Z_to_bv 64 (S + Z.of_nat i + 1) ->
    xa6 = Z_to_bv 64 1 -> xs0 = Z_to_bv 64 (D + Z.of_nat i) ->
    evt rsegs POST (ST 0x24ae4 m1 x1 x5 x6 x7 x10 xa1 xa2 x13 x14 xa5 xa6 x17 xs0 x28 x29 x30 x31).
  Proof. intros; subst; eapply (sp_head (nn - i) i); eauto. Qed.

  #[using="NONUL PAD SEP SEPD SEPS LO BND"] Lemma sp_body : forall bs,
    mem_inv rsegs m -> u8arr rsegs m D bs -> length bs = nn -> bytes_at rsegs m S full -> stk rsegs m lo SP ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x24a88) fc None m (seg_rom rsegs)).
  Proof.
    intros bs MI DST LBS SRC STK. pose proof bounds as B.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1; cbn in R1.
    carve_frame 16%nat STK.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (I : INV mm 0 bs) end.
    { split; [exact DST|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact SRC| split; [exact MI| split; [exact MU| split; [exact WM| split; [exact STK| exact FR]]]]]. }
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    -
      zstep. zstep. zstep. if_cases Ksal; zify_cond Ksal.
      + eapply (sp_mid' 0 _ bs); [lia| exact I| | | reg_eq| reg_eq| reg_eq].
        * rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
        * intros _. revert Ksal. zb_masks. intros Ksal. rewrite Z.add_0_r. Z.div_mod_to_equations. lia.
      + zstep. if_cases Kn0; zify_cond Kn0.
        * eapply (sp_mid' 0 _ bs); [lia| exact I| | | reg_eq| reg_eq| reg_eq].
          -- rewrite b2z_word_zero_iff, Z.ltb_ge. lia.
          -- rewrite b2z_word_zero_iff, Z.ltb_ge. intros. exfalso. lia.
        * zstep. zstep. eapply (sp_head' 0 _ bs); [lia| exact I| reg_eq| reg_eq| reg_eq| reg_eq| reg_eq].
    - eapply (sp_bentry' 0 _ bs); [lia| exact I| reg_eq| reg_eq| reg_eq].
  Qed.
End Proofs.

Lemma stpncpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack bs : list byte) (lo : Z),
  u8arr rsegs m (bv_unsigned a0) bs -> length bs = Z.to_nat (bv_unsigned a2) ->
  bytes_at rsegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1 \/ bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z ->
  mem_inv rsegs m ->
  evt rsegs (stpncpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24a88) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros DST LBS SRC NONUL PAD STK LO SEP SEPD SEPS DN MI.
  eapply sp_body; try eassumption.
  pose proof (u8arr_bound _ _ _ _ DST) as B1. pose proof (bytes_at_bound _ _ _ _ SRC) as B2. rewrite app_length in B2. cbn [length] in B2.
  destruct STK as [? _]. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2; cbn in R2. lia.
Qed.

Definition strncpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ u8arr rsegs m' (bv_unsigned a0) (stpn_result str (Z.to_nat (bv_unsigned a2)))
    /\ bytes_at rsegs m' (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).

Lemma strncpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack bs : list byte) (lo : Z),
  u8arr rsegs m (bv_unsigned a0) bs -> length bs = Z.to_nat (bv_unsigned a2) ->
  bytes_at rsegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1 \/ bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strncpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24a60) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros DST LBS SRC NONUL PAD STK LO SEP SEPD SEPS DN MI.
  pose proof (u8arr_bound _ _ _ _ DST) as B1. pose proof (bytes_at_bound _ _ _ _ SRC) as B2. rewrite app_length in B2. cbn [length] in B2.
  pose proof STK as STK0. destruct STK0 as [LO0 _]. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2; cbn in R2.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat STK.
  do 5 zstep.
  pose proof (unsigned_lit (bv_unsigned sp + -16) ltac:(lia)) as USP.
  call stpncpy_spec.
  1:{ exact DST. } 1:{ exact LBS. } 1:{ exact SRC. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ rewrite USP. exact STK. }
  all: rewrite ?USP; try lia. 1:{ exact MI. }
  do 5 zstep.
  rewrite ?USP in *.
  lazymatch goal with H : stk _ ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => release_frame FR H (bv_unsigned sp) end.
  finish.
Qed.
