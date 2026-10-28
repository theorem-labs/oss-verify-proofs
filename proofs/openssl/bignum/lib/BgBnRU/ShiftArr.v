(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma nth_firstn_lt : forall (l : list Z) k j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
  intros l k j d H. revert l j H. induction k as [|k IH]; intros l j H; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition ursh_m (n : Z) : Z := Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63.
Lemma ursh_m_eqg : forall n lb, (0 <= n < 2147483648)%Z -> Z.land n 63 = lb -> ursh_m n = ((64 - lb) mod 64)%Z.
Proof.
  intros n lb H <-. unfold ursh_m. rewrite (bn_swrap32_small (0 - n)) by lia.
  change 63%Z with (Z.ones 6). rewrite !Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma ulimbs_at_cons_write : forall m A v l,
  limbs_at bgusegs m (A + 8) l -> (0 <= A)%Z ->
  limbs_at bgusegs (write_to_mem m (wa A) (le8 (Z_to_bv 64 v))) A (v :: l).
Proof.
  intros m A v l H HA. pose proof (limbs_at_bound _ _ _ _ H) as B.
  change (v :: l) with ([v] ++ l). apply limbs_at_app. split.
  - unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - cbn [length]. apply limbs_at_write_other; [exact H | lia | rewrite length_le8; lia | rewrite length_le8; right; lia].
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp Dr nw8 n lb nn : Z).
  Notation top := (Z.of_nat (length f)).
  Notation T := (Dr + nw8)%Z.
  Hypothesis Hn : (0 <= n < 2147483648)%Z.
  Hypothesis Hlb : (0 <= lb < 64)%Z.
  Hypothesis Elb : Z.land n 63 = lb.
  Hypothesis Hnn : (0 <= nn < 18446744073709551616)%Z.
  Hypothesis Enn : (nn mod 64 = (64 - lb) mod 64)%Z.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis Hfp : (8 <= fp)%Z.
  Hypothesis HDr : (0 <= Dr)%Z.
  Hypothesis Hnw8 : (0 <= nw8)%Z.
  Hypothesis DISJ : (fp <= T \/ T + 8 * (top + 1) <= fp)%Z.
  Hypothesis UBT : (0 < Dr /\ Dr mod 8 = 0 /\ nw8 mod 8 = 0 /\ fp mod 8 = 0)%Z.

  Notation rb := ((64 - lb) mod 64)%Z.
  Notation rmask := (if (lb =? 0)%Z then 0 else 18446744073709551615)%Z.

  (* [comment removed for export] *)
  Notation SH pc mm x5 x6 x7 x12 x13 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 Dr) (Z_to_bv 64 T) x12 x13 (Z_to_bv 64 1) (Z_to_bv 64 fp) x16 x17 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Notation W := [(T, T + 8 * (top + 1))]%Z.

  Definition SINVG (m1 : word -> option byte) (i : nat) : Prop :=
    limbs_at bgusegs m1 (T + 8 * Z.of_nat i) (map (lsh_at f lb) (seq i (S (length f) - i))) /\ limbs_at bgusegs m1 fp (firstn i f) /\
    wr_at bgusegs m1 T (8 * (top + 1)) /\ mem_inv bgusegs m1 /\ munch W m m1 /\ wmono bgusegs m m1.

  Lemma SINVG_store : forall m1 i v,
    SINVG m1 (S i) -> (i <= length f)%nat -> v = lsh_at f lb i ->
    store_ok bgusegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
    SINVG (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) i.
  Proof using All.
    intros m1 i v (HW & HF & WT & MI & MU & WM) Hi ->.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgusegs m1 T (8 * (top + 1)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (L8 : length (le8 (Z_to_bv 64 (lsh_at f lb i))) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgusegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
    { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok bgusegs m1 T (8 * (top + 1))); [exact WT | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)).
    unfold SINVG.
    split. { replace (S (length f) - i)%nat with (S (S (length f) - S i)) by lia. cbn [seq map].
             apply ulimbs_at_cons_write; [|lia]. replace (T + 8 * Z.of_nat i + 8)%Z with (T + 8 * Z.of_nat (S i))%Z by lia. exact HW. }
    split. { rewrite <- (firstn_skipn i (firstn (S i) f)) in HF. apply limbs_at_app in HF. destruct HF as [HF1 _].
             rewrite firstn_firstn in HF1. replace (Nat.min i (S i)) with i in HF1 by lia.
             pose proof (limbs_at_bound _ _ _ _ HF1) as BF1.
             apply limbs_at_write_other; [exact HF1 | lia | rewrite L8; lia | rewrite L8 ].
             rewrite length_firstn. clear - DISJ Hi Hnw8 HDr Hfp. lia. }
    split. { apply wr_at_write. exact WT. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  Lemma lshg_tail : forall m1 x5 x6 x7 x12 x13 x17 x28 x30 x31,
    SINVG m1 1 ->
    (forall m2 x5 x6 x7 x13 x16 x17 x28 x29 x30 x31,
       limbs_at bgusegs m2 T (map (lsh_at f lb) (seq 0 (S (length f)))) -> mem_inv bgusegs m2 ->
       munch [(T, T + 8 * (top + 1))]%Z m m2 -> wmono bgusegs m m2 ->
       evt bgusegs POST (SH 0x10a470 m2 x5 x6 x7 x12 x13 x16 x17 x28 x29 x30 x31)) ->
    evt bgusegs POST (SH 0x10a460 m1 x5 x6 x7 x12 x13 (Z_to_bv 64 lb) x17 x28 (Z_to_bv 64 (nth 0 f 0%Z)) x30 x31).
  Proof.
    intros m1 x5 x6 x7 x12 x13 x17 x28 x30 x31 I K.
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    pose proof I as (_ & _ & WT0 & MI0 & _).
    pose proof (wr_at_below bgusegs m1 T (8 * (top + 1)) MI0 WT0 ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (TR : (0 < T < 18446744073709551616)%Z) by (clear - TOPB UBT Htop HDr Hnw8; lia).
    clear WT0 MI0 TOPB.
    zstep. rewrite (land7 T) by (clear - UBT HDr Hnw8; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep.
    setreg 13%Z (Z_to_bv 64 (lsh_at f lb 0))
      ltac:(apply Z_to_bv_eqm; rewrite (lsh_at_0 f lb ltac:(lia)), <- (shlw_machine lb _ Hlb); change (2 ^ 64)%Z with 18446744073709551616%Z;
            rewrite Z.mod_mod by lia; reflexivity).
    destruct (SINVG_store m1 0%nat _ I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat 0)%Z with T in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & HF & WT & MI & MU & WM).
    replace (T + 8 * Z.of_nat 0)%Z with T in HW by lia. replace (S (length f) - 0)%nat with (S (length f)) in HW by lia.
    apply K; assumption.
  Qed.

  (* [comment removed for export] *)
  Notation ND := (Z.lxor fp 18446744073709551615).
  Notation HEAD mm j x12 x29 x30 x31 :=
    (SH 0x10a3c0 mm (Z_to_bv 64 rb) (Z_to_bv 64 (nth (S j) f 0%Z)) (Z_to_bv 64 rmask) x12 (Z_to_bv 64 (Z.of_nat (S (S j)))) (Z_to_bv 64 lb) (Z_to_bv 64 ND)
        (Z_to_bv 64 1) x29 x30 x31).
  Notation KEXIT x12 :=
    (forall m2 x5 x6 x7 x13 x17 x28 x30 x31,
       SINVG m2 1 ->
       evt bgusegs POST (SH 0x10a460 m2 x5 x6 x7 x12 x13 (Z_to_bv 64 lb) x17 x28 (Z_to_bv 64 (nth 0 f 0%Z)) x30 x31)).

  Lemma lshg_round : forall (j : nat) m1 x12 x29 x30 x31,
    (S j < length f)%nat -> SINVG m1 (S (S j)) ->
    (j = 0%nat -> KEXIT x12) ->
    (forall j', j = S j' -> forall m2 x29 x30 x31, SINVG m2 (S (S j')) -> evt bgusegs POST (HEAD m2 j' x12 x29 x30 x31)) ->
    evt bgusegs POST (HEAD m1 j x12 x29 x30 x31).
  Proof.
    intros j m1 x12 x29 x30 x31 Hj I KE KL.
    pose proof I as (_ & HF & WT & MI & _).
    pose proof (limbs_at_bound _ _ _ _ HF) as BF. rewrite length_firstn in BF.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgusegs m1 T (8 * (top + 1)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (RS : (0 <= nth (S j) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RJ : (0 <= nth j f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NJ : nth_error (firstn (S (S j)) f) j = Some (nth j f 0%Z)).
    { rewrite <- (nth_firstn_lt f (S (S j)) j 0%Z) by lia. apply nth_error_nth'. rewrite length_firstn. lia. }
    assert (END : (Z.lxor fp 18446744073709551615 = 18446744073709551615 - fp)%Z) by (apply zb_lxor_ones; change (2 ^ 64)%Z with 18446744073709551616%Z in BF; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat (S (S j)) + -2)) by (clear - Hj Htop; lia).
    replace (Z.of_nat (S (S j)) + -2)%Z with (Z.of_nat j) by (clear; lia).
    zstep. replace (Z.of_nat j ≪ 3)%Z with (8 * Z.of_nat j)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    chk ltac:(fun C => rewrite END in C; clear - C BF Hj; change (2 ^ 64)%Z with 18446744073709551616%Z in BF; lia).
    zstep. rewrite (bn_swrap32_small (Z.of_nat (S (S j)) + -1)) by (clear - Hj Htop; lia).
    replace (Z.of_nat (S (S j)) + -1)%Z with (Z.of_nat (S j)) by (clear; lia).
    zstep. replace (Z.of_nat (S j) ≪ 3)%Z with (8 * Z.of_nat (S j))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. replace (8 * Z.of_nat (S j) + T)%Z with (T + 8 * Z.of_nat (S j))%Z by (clear; lia).
    chk ltac:(fun C => clear - C T0 TOPB Hj; lia).
    zstep. replace (T + 8 * Z.of_nat (S j) <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - T0; lia).
    cbn [Z.b2z]. zstep. cbn [Z.lxor].
    chk ltac:(fun C => clear - C; lia).
    zstep.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs m1 fp (firstn (S (S j)) f) j _ ad HF NJ ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 4 zstep.
    setreg 6%Z (Z_to_bv 64 (lsh_at f lb (S j)))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (lsh_cy_machine lb _ Hlb RJ), (shlw_machine lb _ Hlb), (lsh_at_mid f lb j Hj); reflexivity).
    destruct (SINVG_store m1 (S j) _ I ltac:(lia) eq_refl) as [SOK I1].
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
      zstep. if_cases KA; zify_cond KA. 2:{ exfalso. clear - KA UBT HDr Hnw8. lia. }
      eapply KE; [reflexivity | exact I1].
  Qed.

  Lemma lshg_loop : forall (j : nat) m1 x12 x29 x30 x31,
    (S j < length f)%nat -> SINVG m1 (S (S j)) -> KEXIT x12 -> evt bgusegs POST (HEAD m1 j x12 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros m1 x12 x29 x30 x31 Hj I K.
    - eapply lshg_round; [exact Hj | exact I | intros _; exact K | intros j' E; discriminate E].
    - eapply lshg_round; [exact Hj | exact I | intros E; discriminate E | ].
      intros j' E m2 y29 y30 y31 I2. injection E as <-. eapply IH; [lia | exact I2 | exact K].
  Qed.

  Lemma lshg_block : forall x6 x7 x12 x16 x29 x30 x31,
    limbs_at bgusegs m fp f -> wr_at bgusegs m T (8 * (top + 1)) -> mem_inv bgusegs m ->
    (forall m2 x5 x6 x7 x13 x16 x17 x28 x29 x30 x31,
       limbs_at bgusegs m2 T (map (lsh_at f lb) (seq 0 (S (length f)))) -> mem_inv bgusegs m2 ->
       munch [(T, T + 8 * (top + 1))]%Z m m2 -> wmono bgusegs m m2 ->
       evt bgusegs POST (SH 0x10a470 m2 x5 x6 x7 x12 x13 x16 x17 x28 x29 x30 x31)) ->
    evt bgusegs POST (SH 0x10a38c m (Z_to_bv 64 (fp + 8 * (top - 1))) x6 x7 x12 (Z_to_bv 64 top) x16 (Z_to_bv 64 (top - 1)) (Z_to_bv 64 (T + 8 * top)) x29 x30 x31).
  Proof using All.
    intros x6 x7 x12 x16 x29 x30 x31 HF WT MI K.
    pose proof (limbs_at_bound _ _ _ _ HF) as BF.
    pose proof (wr_at_below bgusegs m T (8 * (top + 1)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    do 2 zstep.
    rewrite Elb.
    (* [comment removed for export] *)
    assert (NL : nth_error f (length f - 1) = Some (nth (length f - 1) f 0%Z)) by (apply nth_error_nth'; lia).
    assert (RL : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgusegs m fp f (length f - 1) _ ad HF NL ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    zstep.
    change (Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63) with (ursh_m n). rewrite (ursh_m_eqg n lb Hn Elb).
    do 3 zstep.
    change (Z.lor (((0 - rb) mod 18446744073709551616) ≫ 8) ((0 - rb) mod 18446744073709551616)) with (rmask_m rb).
    rewrite (rmask_m_eq lb Hlb).
    do 2 zstep.
    assert (ETOP : lsh_at f lb (length f) = lsh_cy lb (nth (length f - 1) f 0%Z)).
    { rewrite lsh_at_top. destruct (length f) as [|j] eqn:E; [exfalso; lia|]. f_equal. f_equal. lia. }
    setreg 29%Z (Z_to_bv 64 (lsh_at f lb (length f)))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (lsh_cy_machine lb _ Hlb RL), ETOP; reflexivity).
    assert (I0 : SINVG m (S (length f))).
    { unfold SINVG. replace (S (length f) - S (length f))%nat with 0%nat by lia. cbn [seq map].
      split; [apply limbs_at_nil; lia|]. split; [rewrite firstn_all2 by lia; exact HF|]. split; [exact WT|]. split; [exact MI|]. split; [apply munch_refl | apply wmono_refl]. }
    destruct (SINVG_store m (length f) _ I0 ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m1 end.
    clear SOK I0 HF WT MI. try clear m.
    zstep. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      assert (E1 : length f = 1%nat).
      { apply andb_false_iff in KT. destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia. }
      replace (length f - 1)%nat with 0%nat by lia.
      zstep.

      chk ltac:(fun C => clear - C UBT HDr Hnw8; lia).
      eapply lshg_tail; [ | exact K]. rewrite E1 in I1. exact I1.
    - zstep. zstep.
      assert (E2 : (length f - 1 = S (length f - 2))%nat) by lia.
      replace top with (Z.of_nat (S (S (length f - 2)))) at 1 by lia.
      rewrite E2.
      eapply lshg_loop; [lia | | ].
      + replace (S (S (length f - 2))) with (length f) by lia. exact I1.
      + intros m2 y5 y6 y7 y13 y17 y28 y30 y31 I2. eapply lshg_tail; [exact I2 | exact K].
  Qed.
(* [comment removed for export] *)
End Block.
