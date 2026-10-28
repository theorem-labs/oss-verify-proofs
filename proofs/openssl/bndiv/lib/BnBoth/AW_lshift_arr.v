(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import ShiftPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2247672 => 2
  | 2247684 => 1
  | 2247688 => 2
  | 2247752 => 1
  | 2247756 => 2
  | 2247760 => 1
  | 2247768 => 2
  | 2247796 => 1
  | 2247828 => 2
  | 2247832 => 2
  | 2247860 => 1
  | 2247864 => 2
  | 2247868 => 1
  | 2247872 => 1
  | 2247876 => 1
  | 2247880 => 1
  | 2247884 => 2
  | 2247892 => 2
  | 2247908 => 1
  | 2247912 => 1
  | 2247916 => 2
  | 2247920 => 1
  | 2247924 => 1
  | 2247928 => 1
  | 2247932 => 1
  | 2247936 => 2
  | 2247940 => 2
  | 2247944 => 1
  | 2247948 => 2
  | 2247976 => 1
  | 2247980 => 2
  | 2247984 => 1
  | 2247988 => 1
  | 2247992 => 1
  | 2247996 => 1
  | 2248000 => 2
  | 2248004 => 1
  | 2248008 => 2
  | 2248072 => 1
  | 2248088 => 2
  | 2248104 => 2
  | 2248108 => 1
  | 2248112 => 1
  | 2248116 => 2
  | 2248196 => 2
  | 2248200 => 2
  | 2248224 => 1
  | 2248228 => 1
  | 2248232 => 2
  | 2248252 => 2
  | 2248256 => 2
  | 2248260 => 1
  | 2248264 => 2
  | 2248296 => 2
  | 2248300 => 1
  | 2248304 => 2
  | 2248344 => 2
  | 2248348 => 2
  | 2248376 => 2
  | 2248380 => 2
  | 2248448 => 1
  | 2248452 => 2
  | 2248456 => 1
  | 2248464 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

(* [comment removed for export] *)
Lemma limbs_at_cons_writeA : forall m A v l,
  limbs_at bsegs m (A + 8) l -> (0 <= A)%Z ->
  limbs_at bsegs (write_to_mem m (wa A) (le8 (Z_to_bv 64 v))) A (v :: l).
Proof.
  intros m A v l H HA. pose proof (limbs_at_bound _ _ _ _ H) as B.
  change (v :: l) with ([v] ++ l). apply limbs_at_app. split.
  - unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - cbn [length]. apply limbs_at_write_other; [exact H | lia | rewrite length_le8; lia | rewrite length_le8; right; lia].
Qed.

(* [comment removed for export] *)
Definition negn_mA (n : Z) : Z := Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63.
Lemma negn_chkA : forallb (fun n => negn_mA n =? (64 - n) mod 64)%Z (map Z.of_nat (seq 0 64)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma negn_mA_eq : forall n, (0 <= n < 64)%Z -> negn_mA n = ((64 - n) mod 64)%Z.
Proof.
  intros n H. pose proof negn_chkA as A. rewrite forallb_forall in A. specialize (A n). rewrite Z.eqb_eq in A. apply A.
  apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 a4 s2 s3 s6 s7 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp T n : Z).
  Notation top := (Z.of_nat (length f)).
  Hypothesis Hn : (0 <= n < 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis DISJ : (fp + 8 * top <= T \/ T + 8 * (top + 1) <= fp)%Z.
  (* [comment removed for export] *)
  Hypothesis ACF : acc bsegs m fp (8 * top).
  Hypothesis ACT : acc bsegs m T (8 * (top + 1)).
  Hypothesis ALF : (fp mod 8 = 0)%Z.
  Hypothesis ALT : (T mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * (top + 1))]%Z.
  Hypothesis T0 : (0 < T)%Z.

  Notation rb := ((64 - n) mod 64)%Z.
  Notation rmask := (if (n =? 0)%Z then 0 else 18446744073709551615)%Z.
  (* [comment removed for export] *)
  Notation SH pc mm x6 x7 x11 x13 x15 x25 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 fp) x6 x7 s0 s1 (Z_to_bv 64 T) x11 (Z_to_bv 64 0) x13 a4 x15 (Z_to_bv 64 T) (Z_to_bv 64 1) s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 SHB)
             s6 s7 s8 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation W := [(T, T + 8 * (top + 1))]%Z.
  (* [comment removed for export] *)
  Definition SINV (m1 : word -> option byte) (i : nat) : Prop :=
    limbs_at bsegs m1 (T + 8 * Z.of_nat i) (map (lsh_at f n) (seq i (S (length f) - i))) /\ limbs_at bsegs m1 fp f /\
    wr_at bsegs m1 T (8 * (top + 1)) /\ mem_inv bsegs m1 /\ munch W m m1 /\ wmono bsegs m m1.
  (* [comment removed for export] *)
  Definition BND : Prop := ((0 <= fp /\ fp + 8 * top <= 140737488355328) /\ (0 <= T /\ T + 8 * (top + 1) <= 140737488355328))%Z.

  Lemma SINV_store : forall m1 i v,
    SINV m1 (S i) -> (i <= length f)%nat -> v = lsh_at f n i ->
    store_ok bsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
    SINV (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) i.
  Proof using DISJ Htop.
    intros m1 i v (HW & HF & WT & MI & MU & WM) Hi ->.
    pose proof (limbs_at_bound _ _ _ _ HF) as BF.
    assert (T0' : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bsegs m1 T (8 * (top + 1)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (L8 : length (le8 (Z_to_bv 64 (lsh_at f n i))) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
    { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok bsegs m1 T (8 * (top + 1))); [exact WT | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)).
    unfold SINV.
    split. { replace (S (length f) - i)%nat with (S (S (length f) - S i)) by lia. cbn [seq map].
             apply limbs_at_cons_writeA; [|lia]. replace (T + 8 * Z.of_nat i + 8)%Z with (T + 8 * Z.of_nat (S i))%Z by lia. exact HW. }
    split. { apply limbs_at_write_other; [exact HF | lia | rewrite L8; lia | rewrite L8; lia]. }
    split. { apply wr_at_write. exact WT. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma shF : forall m1 i (k : nat) ad, BND -> SINV m1 i -> (k < length f)%nat -> ad = wa (shad (fp + 8 * Z.of_nat k)) ->
    ov_read_bytes bsegs m1 ad 1 = Some [z8].
  Proof using ACF ALF OFFT.
    intros m1 i k ad (BF & _) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bsegs _ m m1 fp top 0 (Z.of_nat k) _ ACF MU OFFT ALF BF); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.
  Lemma shT : forall m1 i (k : nat) ad, BND -> SINV m1 i -> (k <= length f)%nat -> ad = wa (shad (T + 8 * Z.of_nat k)) ->
    ov_read_bytes bsegs m1 ad 1 = Some [z8].
  Proof using ACT ALT OFFT.
    intros m1 i k ad (_ & BT) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bsegs _ m m1 T (top + 1) 0 (Z.of_nat k) _ ACT MU OFFT ALT BT); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  Notation ND := (Z.lxor fp 18446744073709551615).
  (* [comment removed for export] *)
  Notation HEAD mm j x11 x13 x25 :=
    (SH 0x224d90 mm (Z_to_bv 64 n) (Z_to_bv 64 ND) x11 x13 (Z_to_bv 64 (Z.of_nat (S (S j)))) x25
        (Z_to_bv 64 rb) (Z_to_bv 64 (nth (S j) f 0%Z)) (Z_to_bv 64 rmask) (Z_to_bv 64 1)).
  Notation KEXIT :=
    (forall m2 x11 x25,
       SINV m2 1 ->
       evt bsegs POST (SH 0x224e6c m2 (Z_to_bv 64 n) (Z_to_bv 64 ND) x11 (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 1) x25
                           (Z_to_bv 64 rb) (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 rmask) (Z_to_bv 64 1))).

  Lemma lsh_round : forall (j : nat) m1 x11 x13 x25,
    BND -> (S j < length f)%nat -> SINV m1 (S (S j)) ->
    (j = 0%nat -> KEXIT) ->
    (forall j', j = S j' -> forall m2 x11 x13 x25, SINV m2 (S (S j')) -> evt bsegs POST (HEAD m2 j' x11 x13 x25)) ->
    evt bsegs POST (HEAD m1 j x11 x13 x25).
  Proof.
    intros j m1 x11 x13 x25 B Hj I KE KL.
    pose proof I as (_ & HF & WT & MI & _).
    pose proof B as ((BF1 & BF2) & (BT1 & BT2)).
    assert (RS : (0 <= nth (S j) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RJ : (0 <= nth j f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NJ : nth_error f j = Some (nth j f 0%Z)) by (apply nth_error_nth'; lia).
    assert (END : (Z.lxor fp 18446744073709551615 = 18446744073709551615 - fp)%Z) by (apply zb_lxor_ones; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat (S (S j)) + -2)) by (clear - Hj Htop; lia).
    replace (Z.of_nat (S (S j)) + -2)%Z with (Z.of_nat j) by (clear; lia).
    zstep. replace (Z.shiftl (Z.of_nat j) 3)%Z with (8 * Z.of_nat j)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    chk ltac:(fun C => rewrite END in C; clear - C BF1 BF2 Hj; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat (S (S j)) + -1)) by (clear - Hj Htop; lia).
    replace (Z.of_nat (S (S j)) + -1)%Z with (Z.of_nat (S j)) by (clear; lia).
    zstep. replace (Z.shiftl (Z.of_nat (S j)) 3)%Z with (8 * Z.of_nat (S j))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. replace (8 * Z.of_nat (S j) + T)%Z with (T + 8 * Z.of_nat (S j))%Z by (clear; lia).
    ub. zstep.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shF m1 _ j ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ (S j) ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bsegs m1 fp f j _ ad HF NJ ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 4 zstep.
    setreg 29%Z (Z_to_bv 64 (lsh_at f n (S j)))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (lsh_cy_machine n _ Hn RJ), (shlw_machine n _ Hn), (lsh_at_mid f n j Hj); reflexivity).
    destruct (SINV_store m1 (S j) _ I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HF WT MI. try clear m1.
    zstep.
    zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      destruct j as [|j']; [exfalso; clear - KB; lia|].
      eapply KL; [reflexivity | exact I1].
    - (* [comment removed for export] *)
      assert (j = 0%nat) by (clear - KB; lia). subst j.
      zstep. if_cases KA; zify_cond KA. 2:{ exfalso. clear - KA T0 BT1 BT2 Htop. rewrite ?unsigned_lit in KA by lia. lia. }
      eapply KE; [reflexivity | exact I1].
  Qed.

  Lemma lsh_loop : forall (j : nat) m1 x11 x13 x25,
    BND -> (S j < length f)%nat -> SINV m1 (S (S j)) -> KEXIT -> evt bsegs POST (HEAD m1 j x11 x13 x25).
  Proof.
    induction j as [|j IH]; intros m1 x11 x13 x25 B Hj I K.
    - eapply lsh_round; [exact B | exact Hj | exact I | intros _; exact K | intros j' E; discriminate E].
    - eapply lsh_round; [exact B | exact Hj | exact I | intros E; discriminate E | ].
      intros j' E m2 y11 y13 y25 I2. injection E as <-. eapply IH; [exact B | lia | exact I2 | exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma lsh_tail : forall m1 x7 x11 x15 x25 x28 x29 x30 x31,
    BND -> SINV m1 1 ->
    (forall m2 x6 x7 x11 x13 x15 x25 x28 x29 x30 x31,
       limbs_at bsegs m2 T (map (lsh_at f n) (seq 0 (S (length f)))) -> limbs_at bsegs m2 fp f -> mem_inv bsegs m2 ->
       munch [(T, T + 8 * (top + 1))]%Z m m2 -> wmono bsegs m m2 ->
       evt bsegs POST (SH 0x224e8c m2 x6 x7 x11 x13 x15 x25 x28 x29 x30 x31)) ->
    evt bsegs POST (SH 0x224e6c m1 (Z_to_bv 64 n) x7 x11 (Z_to_bv 64 (nth 0 f 0%Z)) x15 x25 x28 x29 x30 x31).
  Proof.
    intros m1 x7 x11 x15 x25 x28 x29 x30 x31 B I K.
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    pose proof B as ((BF1 & BF2) & (BT1 & BT2)).
    ub. do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ 0%nat ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    zstep.
    setreg 11%Z (Z_to_bv 64 (lsh_at f n 0))
      ltac:(apply Z_to_bv_eqm; rewrite (lsh_at_0 f n ltac:(lia)), <- (shlw_machine n _ Hn); change (2 ^ 64)%Z with 18446744073709551616%Z;
            rewrite Z.mod_mod by lia; reflexivity).
    destruct (SINV_store m1 0%nat _ I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat 0)%Z with T in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & HF & WT & MI & MU & WM).
    replace (T + 8 * Z.of_nat 0)%Z with T in HW by lia. replace (S (length f) - 0)%nat with (S (length f)) in HW by lia.
    apply K; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma lsh_blockA : forall x6 x25 x28 x29 x30 x31,
    limbs_at bsegs m fp f -> wr_at bsegs m T (8 * (top + 1)) -> mem_inv bsegs m ->
    (forall m2 x6 x7 x11 x13 x15 x25 x28 x29 x30 x31,
       limbs_at bsegs m2 T (map (lsh_at f n) (seq 0 (S (length f)))) -> limbs_at bsegs m2 fp f -> mem_inv bsegs m2 ->
       munch [(T, T + 8 * (top + 1))]%Z m m2 -> wmono bsegs m m2 ->
       evt bsegs POST (SH 0x224e8c m2 x6 x7 x11 x13 x15 x25 x28 x29 x30 x31)) ->
    evt bsegs POST (SH 0x224d5c m x6 (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (fp + 8 * (top - 1))) (Z_to_bv 64 (T + 8 * top)) (Z_to_bv 64 top) x25 x28 x29 x30 x31).
  Proof.
    intros x6 x25 x28 x29 x30 x31 HF WT MI K.
    pose proof (limbs_at_bound _ _ _ _ HF) as BF.
    pose proof (wr_at_below bsegs m T (8 * (top + 1)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (TZ : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    assert (B : BND).
    { split; [exact (limbs_at_b47 bsegs m fp f HF MI ltac:(lia)) |].
      pose proof (wr_at_b47 bsegs m T (8 * (top + 1)) WT MI ltac:(lia)) as H. lia. }
    pose proof B as ((BF1 & BF2) & (BT1 & BT2)).
    do 2 zstep.
    replace (Z.land n 63) with n by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 6)%Z with 64%Z; lia).
    (* [comment removed for export] *)
    assert (NL : nth_error f (length f - 1) = Some (nth (length f - 1) f 0%Z)) by (apply nth_error_nth'; lia).
    assert (RL : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bsegs m fp f (length f - 1) _ ad HF NL ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    zstep.
    change (Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63) with (negn_mA n). rewrite (negn_mA_eq n Hn).
    do 3 zstep.
    change (Z.lor (((0 - rb) mod 18446744073709551616) ≫ 8) ((0 - rb) mod 18446744073709551616)) with (rmask_m rb).
    rewrite (rmask_m_eq n Hn).
    do 2 zstep.
    assert (ETOP : lsh_at f n (length f) = lsh_cy n (nth (length f - 1) f 0%Z)).
    { rewrite lsh_at_top. destruct (length f) as [|j] eqn:E; [exfalso; lia|]. f_equal. f_equal. lia. }
    setreg 11%Z (Z_to_bv 64 (lsh_at f n (length f)))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (lsh_cy_machine n _ Hn RL), ETOP; reflexivity).
    assert (I0 : SINV m (S (length f))).
    { unfold SINV. replace (S (length f) - S (length f))%nat with 0%nat by lia. cbn [seq map].
      split; [apply limbs_at_nil; lia|]. split; [exact HF|]. split; [exact WT|]. split; [exact MI|]. split; [apply munch_refl | apply wmono_refl]. }
    destruct (SINV_store m (length f) _ I0 ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * top)%Z with (T + 8 * Z.of_nat (length f))%Z by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m1 end.
    clear SOK I0 HF WT MI. try clear m.
    zstep. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      assert (E1 : length f = 1%nat).
      { rewrite ?signed_small in KT by lia. lia. }
      replace (length f - 1)%nat with 0%nat by lia.
      zstep. ub1 ub_kind.
      eapply lsh_tail; [exact B | | exact K]. rewrite E1 in I1. exact I1.
    - ub. zstep.
      assert (E2 : (length f - 1 = S (length f - 2))%nat) by lia.
      replace top with (Z.of_nat (S (S (length f - 2)))) at 1 by lia.
      rewrite E2.
      eapply lsh_loop; [exact B | lia | | ].
      + replace (S (S (length f - 2))) with (length f) by lia. exact I1.
      + intros m2 y11 y25 I2. eapply lsh_tail; [exact B | exact I2 | exact K].
  Qed.
End Block.
