(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import AW_lshift_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Lemma nth_firstn_ltA : forall (l : list Z) k j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
  intros l k j d H. revert l j H. induction k as [|k IH]; intros l j H; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma negn_mA_gen : forall n lb, (0 <= n < 2147483648)%Z -> Z.land n 63 = lb -> negn_mA n = ((64 - lb) mod 64)%Z.
Proof.
  intros n lb Hn <-. unfold negn_mA. change 63%Z with (Z.ones 6). rewrite !Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z.
  assert (E : bv_swrap 32 (0 - n) = (0 - n)%Z).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (2 ^ (Z.of_N 32 - 1))%Z with 2147483648%Z.
    destruct (Z.eq_dec n 0) as [->|NZ]; [reflexivity|]. rewrite Z.mod_small by lia. lia. }
  rewrite E. rewrite Z.mod_mod_divide by (exists (2^58)%Z; reflexivity).
  replace (64 - n mod 64)%Z with (- (n mod 64) + 1 * 64)%Z by lia. rewrite Z.mod_add by lia.
  replace (0 - n)%Z with (- n)%Z by lia. rewrite <- (Z.sub_0_l n), <- (Z.sub_0_l (n mod 64)). rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Section Block.
  Variables (ra sp gp tp s0 s1 a4 s2 s3 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (f : list Z) (fp Dr nw8 n lb : Z).
  Notation top := (Z.of_nat (length f)).
  Notation T := (Dr + nw8)%Z.
  Hypothesis Hn : (0 <= n < 2147483648)%Z.
  Hypothesis Hlb : (0 <= lb < 64)%Z.
  Hypothesis Elb : Z.land n 63 = lb.
  Hypothesis Hf : limbs f.
  Hypothesis Htop : (1 <= top < 2147483647)%Z.
  Hypothesis Hfp : (8 <= fp)%Z.
  Hypothesis HDr : (0 <= Dr)%Z.
  Hypothesis Hnw8 : (0 <= nw8)%Z.
  Hypothesis DISJ : (fp <= T \/ T + 8 * (top + 1) <= fp)%Z.

  Hypothesis ACF : acc bgasegs m fp (8 * top).
  Hypothesis ACT : acc bgasegs m T (8 * (top + 1)).
  Hypothesis ALF : (fp mod 8 = 0)%Z.
  Hypothesis ALT : (T mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * (top + 1))]%Z.

  Notation rb := ((64 - lb) mod 64)%Z.
  Notation rmask := (if (lb =? 0)%Z then 0 else 18446744073709551615)%Z.

  Notation SH pc mm x5 x6 x7 x10 x11 x13 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 (Z_to_bv 64 nw8) x13 a4 x15 x16 x17 s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Notation W := [(T, T + 8 * (top + 1))]%Z.

  Definition SINVG (m1 : word -> option byte) (i : nat) : Prop :=
    limbs_at bgasegs m1 (T + 8 * Z.of_nat i) (map (lsh_at f lb) (seq i (S (length f) - i))) /\ limbs_at bgasegs m1 fp (firstn i f) /\
    wr_at bgasegs m1 T (8 * (top + 1)) /\ mem_inv bgasegs m1 /\ munch W m m1 /\ wmono bgasegs m m1.

  Definition BND : Prop := ((0 <= fp /\ fp + 8 * top <= 140737488355328) /\ (0 <= T /\ T + 8 * (top + 1) <= 140737488355328))%Z.

  Lemma SINVG_store : forall m1 i v,
    SINVG m1 (S i) -> (i <= length f)%nat -> v = lsh_at f lb i ->
    store_ok bgasegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true /\
    SINVG (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) i.
  Proof using DISJ Htop Hfp HDr Hnw8.
    intros m1 i v (HW & HF & WT & MI & MU & WM) Hi ->.
    assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
    pose proof (wr_at_below bgasegs m1 T (8 * (top + 1)) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
    assert (L8 : length (le8 (Z_to_bv 64 (lsh_at f lb i))) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgasegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat i)) 8 = true).
    { change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)). apply (wr_at_store_ok bgasegs m1 T (8 * (top + 1))); [exact WT | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (T + 8 * Z.of_nat i)) with (wa (T + 8 * Z.of_nat i)).
    unfold SINVG.
    split. { replace (S (length f) - i)%nat with (S (S (length f) - S i)) by lia. cbn [seq map].
             apply limbs_at_cons_writeA; [|lia]. replace (T + 8 * Z.of_nat i + 8)%Z with (T + 8 * Z.of_nat (S i))%Z by lia. exact HW. }
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

  Lemma shF : forall m1 i (k : nat) ad, BND -> SINVG m1 i -> (k < length f)%nat -> ad = wa (shad (fp + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof using ACF ALF OFFT.
    intros m1 i k ad (BF & _) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgasegs _ m m1 fp top 0 (Z.of_nat k) _ ACF MU OFFT ALF BF); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.
  Lemma shT : forall m1 i (k : nat) ad, BND -> SINVG m1 i -> (k <= length f)%nat -> ad = wa (shad (T + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof using ACT ALT OFFT.
    intros m1 i k ad (_ & BT) (_ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgasegs _ m m1 T (top + 1) 0 (Z.of_nat k) _ ACT MU OFFT ALT BT); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  Notation HEAD mm j x30 x31 :=
    (SH 0x234504 mm (Z_to_bv 64 rb) (Z_to_bv 64 rmask) (Z_to_bv 64 (Z.of_nat j + 3)) (Z_to_bv 64 T) (Z_to_bv 64 (T + 8 * Z.of_nat (S j)))
        (Z_to_bv 64 (fp + 8 * Z.of_nat j)) (Z_to_bv 64 (nth (S j) f 0%Z)) (Z_to_bv 64 lb) (Z_to_bv 64 2)
        (Z_to_bv 64 (fp + 8 * Z.of_nat j)) (Z_to_bv 64 (T + 8 * Z.of_nat (S j))) x30 x31).
  Notation KEXIT :=
    (forall m2 x7 x11 x13 x28 x29 x30 x31,
       SINVG m2 1 ->
       evt bgasegs POST (SH 0x234554 m2 (Z_to_bv 64 rb) (Z_to_bv 64 rmask) x7 (Z_to_bv 64 T) x11 x13 (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 lb) (Z_to_bv 64 2)
                          x28 x29 x30 x31)).

  Lemma lshg_round : forall (j : nat) m1 x30 x31,
    BND -> (S j < length f)%nat -> SINVG m1 (S (S j)) ->
    (j = 0%nat -> KEXIT) ->
    (forall j', j = S j' -> forall m2 x30 x31, SINVG m2 (S (S j')) -> evt bgasegs POST (HEAD m2 j' x30 x31)) ->
    evt bgasegs POST (HEAD m1 j x30 x31).
  Proof.
    intros j m1 x30 x31 B Hj I KE KL.
    pose proof I as (_ & HF & WT & MI & _).
    pose proof B as (BF & BT).
    assert (RS : (0 <= nth (S j) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (RJ : (0 <= nth j f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    assert (NJ : nth_error (firstn (S (S j)) f) j = Some (nth j f 0%Z)).
    { rewrite <- (nth_firstn_ltA f (S (S j)) j 0%Z) by lia. apply nth_error_nth'. rewrite length_firstn. lia. }
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shF m1 _ j ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ (S j) ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    zstep.
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgasegs m1 fp (firstn (S (S j)) f) j _ ad HF NJ ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 7 zstep.
    setreg 30%Z (Z_to_bv 64 (lsh_at f lb (S j)))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (lsh_cy_machine lb _ Hlb RJ), (shlw_machine lb _ Hlb), (lsh_at_mid f lb j Hj); reflexivity).
    destruct (SINVG_store m1 (S j) _ I ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I HF WT MI. try clear m1.
    zstep.
    zstep. if_cases KB; zify_cond KB.
    -
      destruct j as [|j']; [exfalso; clear - KB; lia|].
      replace (fp + 8 * Z.of_nat (S j') + -8)%Z with (fp + 8 * Z.of_nat j')%Z by lia.
      replace (T + 8 * Z.of_nat (S (S j')) + -8)%Z with (T + 8 * Z.of_nat (S j'))%Z by lia.
      replace (Z.of_nat (S j') + 2)%Z with (Z.of_nat j' + 3)%Z by lia.
      eapply KL; [reflexivity | exact I1].
    -
      assert (j = 0%nat) by (clear - KB; lia). subst j.
      eapply KE; [reflexivity | exact I1].
  Qed.

  Lemma lshg_loop : forall (j : nat) m1 x30 x31,
    BND -> (S j < length f)%nat -> SINVG m1 (S (S j)) -> KEXIT -> evt bgasegs POST (HEAD m1 j x30 x31).
  Proof.
    induction j as [|j IH]; intros m1 x30 x31 B Hj I K.
    - eapply lshg_round; [exact B | exact Hj | exact I | intros _; exact K | intros j' E; discriminate E].
    - eapply lshg_round; [exact B | exact Hj | exact I | intros E; discriminate E | ].
      intros j' E m2 y30 y31 I2. injection E as <-. eapply IH; [exact B | lia | exact I2 | exact K].
  Qed.

  Lemma lshg_tail : forall m1 x7 x11 x13 x28 x29 x30 x31,
    BND -> SINVG m1 1 ->
    (forall m2 x5 x6 x7 x10 x11 x13 x15 x16 x17 x28 x29 x30 x31,
       limbs_at bgasegs m2 T (map (lsh_at f lb) (seq 0 (S (length f)))) -> mem_inv bgasegs m2 ->
       munch [(T, T + 8 * (top + 1))]%Z m m2 -> wmono bgasegs m m2 ->
       evt bgasegs POST (SH 0x234598 m2 x5 x6 x7 x10 x11 x13 x15 x16 x17 x28 x29 x30 x31)) ->
    evt bgasegs POST (SH 0x234554 m1 (Z_to_bv 64 rb) (Z_to_bv 64 rmask) x7 (Z_to_bv 64 T) x11 x13 (Z_to_bv 64 (nth 0 f 0%Z)) (Z_to_bv 64 lb) (Z_to_bv 64 2)
                       x28 x29 x30 x31).
  Proof.
    intros m1 x7 x11 x13 x28 x29 x30 x31 B I K.
    pose proof B as (BF & BT).
    assert (R0 : (0 <= nth 0 f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ 0%nat ad B I ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    zstep.
    setreg 11%Z (Z_to_bv 64 (lsh_at f lb 0))
      ltac:(apply Z_to_bv_eqm; rewrite (lsh_at_0 f lb ltac:(lia)), <- (shlw_machine lb _ Hlb); change (2 ^ 64)%Z with 18446744073709551616%Z;
            rewrite Z.mod_mod by lia; reflexivity).
    destruct (SINVG_store m1 0%nat _ I ltac:(lia) eq_refl) as [SOK I1].
    replace (T + 8 * Z.of_nat 0)%Z with T in SOK, I1 by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    destruct I1 as (HW & HF & WT & MI & MU & WM).
    replace (T + 8 * Z.of_nat 0)%Z with T in HW by lia. replace (S (length f) - 0)%nat with (S (length f)) in HW by lia.
    zstep.
    apply K; assumption.
  Qed.

  Lemma lshg_blockA : forall x5 x6 x10 x11 x15 x16 x17 x31,
    limbs_at bgasegs m fp f -> wr_at bgasegs m T (8 * (top + 1)) -> mem_inv bgasegs m ->
    (forall m2 x5 x6 x7 x10 x11 x13 x15 x16 x17 x28 x29 x30 x31,
       limbs_at bgasegs m2 T (map (lsh_at f lb) (seq 0 (S (length f)))) -> mem_inv bgasegs m2 ->
       munch [(T, T + 8 * (top + 1))]%Z m m2 -> wmono bgasegs m m2 ->
       evt bgasegs POST (SH 0x234598 m2 x5 x6 x7 x10 x11 x13 x15 x16 x17 x28 x29 x30 x31)) ->
    evt bgasegs POST (SH 0x2344a0 m x5 x6 (Z_to_bv 64 top) x10 x11 (Z_to_bv 64 (fp + 8 * top + -8)) x15 x16 x17
                       (Z_to_bv 64 (fp + 8 * top)) (Z_to_bv 64 (8 * top)) (Z_to_bv 64 Dr) x31).
  Proof.
    intros x5 x6 x10 x11 x15 x16 x17 x31 HF WT MI K.
    assert (B : BND).
    { split; [exact (limbs_at_b47 bgasegs m fp f HF MI ltac:(lia)) |].
      pose proof (wr_at_b47 bgasegs m T (8 * (top + 1)) WT MI ltac:(lia)) as H. lia. }
    pose proof B as (BF & BT).
    assert (I0 : SINVG m (S (length f))).
    { unfold SINVG. replace (S (length f) - S (length f))%nat with 0%nat by lia. cbn [seq map].
      split; [apply limbs_at_nil; lia|]. split; [rewrite firstn_all2 by lia; exact HF|]. split; [exact WT|]. split; [exact MI|]. split; [apply munch_refl | apply wmono_refl]. }
    do 4 zstep.
    (let ad := cur_mem_addr in pose proof (shT m _ (length f) ad B I0 ltac:(lia) ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    zstep.

    assert (NL : nth_error f (length f - 1) = Some (nth (length f - 1) f 0%Z)) by (apply nth_error_nth'; lia).
    assert (RL : (0 <= nth (length f - 1) f 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact Hf).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgasegs m fp f (length f - 1) _ ad HF NL ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    do 7 zstep.
    change (Z.land (bv_swrap 32 (0 - n) mod 18446744073709551616) 63) with (negn_mA n). rewrite (negn_mA_gen n lb Hn Elb).
    change (Z.lor (((0 - rb) mod 18446744073709551616) ≫ 8) ((0 - rb) mod 18446744073709551616)) with (rmask_m rb).
    rewrite (rmask_m_eq lb Hlb).
    assert (ETOP : lsh_at f lb (length f) = lsh_cy lb (nth (length f - 1) f 0%Z)).
    { rewrite lsh_at_top. destruct (length f) as [|j] eqn:E; [exfalso; lia|]. f_equal. f_equal. lia. }
    setreg 13%Z (Z_to_bv 64 (lsh_at f lb (length f)))
      ltac:(f_equal; rewrite Z.mod_mod by lia; rewrite (lsh_cy_machine lb _ Hlb RL), ETOP; reflexivity).
    destruct (SINVG_store m (length f) _ I0 ltac:(lia) eq_refl) as [SOK I1].
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m1 end.
    clear SOK I0 HF WT MI. try clear m.
    zstep.
    setreg 16%Z (Z_to_bv 64 lb) ltac:(f_equal; rewrite ?(Z.mod_small n 18446744073709551616) by lia; symmetry; exact Elb).
    zstep. rewrite lts_signed by lia. if_cases KT; zify_cond KT.
    -
      assert (E1 : length f = 1%nat) by lia.
      replace (length f - 1)%nat with 0%nat by lia.
      eapply lshg_tail; [exact B | | exact K]. rewrite E1 in I1. exact I1.
    - do 7 zstep.
      assert (E2 : (length f - 1 = S (length f - 2))%nat) by lia.
      replace (fp + 8 * top + -16)%Z with (fp + 8 * Z.of_nat (length f - 2))%Z by lia.
      replace (T + 8 * top + -8)%Z with (T + 8 * Z.of_nat (S (length f - 2)))%Z by lia.
      replace (nw8 + 8 * top + Dr + -8)%Z with (T + 8 * Z.of_nat (S (length f - 2)))%Z by lia.
      replace (top + 1)%Z with (Z.of_nat (length f - 2) + 3)%Z by lia.
      rewrite E2.
      eapply lshg_loop; [exact B | lia | | ].
      + replace (S (S (length f - 2))) with (length f) by lia. exact I1.
      + intros m2 y7 y11 y13 y28 y29 y30 y31 I2. eapply lshg_tail; [exact B | exact I2 | exact K].
  Qed.
End Block.
