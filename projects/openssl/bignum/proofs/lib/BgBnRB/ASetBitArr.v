(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop AsLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2245656 => 2
  | 2245660 => 1
  | 2245664 => 2
  | 2245808 => 1
  | 2245816 => 1
  | 2245820 => 2
  | 2245824 => 1
  | 2245828 => 1
  | 2245832 => 1
  | 2245836 => 1
  | 2245840 => 2
  | 2245844 => 2
  | 2245848 => 1
  | 2245852 => 2
  | 2245928 => 2
  | 2245932 => 1
  | 2245936 => 1
  | 2245940 => 1
  | 2245944 => 2
  | 2245948 => 2
  | 2245952 => 1
  | 2245956 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition ZINV (m : word -> option byte) (T cnt : Z) (m1 : word -> option byte) (j : nat) : Prop :=
  limbs_at bgbsegs m1 T (repeat 0%Z j) /\ wr_at bgbsegs m1 T (8 * cnt) /\ mem_inv bgbsegs m1 /\
  munch [(T, T + 8 * cnt)]%Z m m1 /\ wmono bgbsegs m m1.

Lemma ZINV_store : forall m T cnt m1 j,
  (Z.of_nat j < cnt)%Z -> ZINV m T cnt m1 j ->
  store_ok bgbsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat j)) 8 = true /\
  ZINV m T cnt (write_to_mem m1 (Z_to_bv 64 (T + 8 * Z.of_nat j)) (le8 (Z_to_bv 64 0))) (S j).
Proof.
  intros m T cnt m1 j Hj (HW & WT & MI & MU & WM).
  assert (T0 : (0 <= T)%Z) by (destruct WT as (W0 & _); exact W0).
  pose proof (wr_at_below bgbsegs m1 T (8 * cnt) MI WT ltac:(lia)) as TOPB. unfold UTOP in TOPB.
  assert (L8 : length (le8 (Z_to_bv 64 0)) = 8%nat) by apply length_le8.
  assert (SOK : store_ok bgbsegs m1 (Z_to_bv 64 (T + 8 * Z.of_nat j)) 8 = true).
  { change (Z_to_bv 64 (T + 8 * Z.of_nat j)) with (wa (T + 8 * Z.of_nat j)). apply (wr_at_store_ok bgbsegs m1 T (8 * cnt)); [exact WT | lia | lia]. }
  split; [exact SOK|].
  change (Z_to_bv 64 (T + 8 * Z.of_nat j)) with (wa (T + 8 * Z.of_nat j)).
  unfold ZINV.
  split. { cbn [repeat]. rewrite repeat_cons.
           replace (T + 8 * Z.of_nat j)%Z with (T + 8 * Z.of_nat (length (repeat 0%Z j)))%Z by (rewrite repeat_length; reflexivity).
           apply limbs_at_snoc_write; [exact HW | rewrite repeat_length; lia]. }
  split. { apply wr_at_write. exact WT. }
  split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
  split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
  apply wmono_write. exact WM.
Qed.

Section Block.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (D top cnt : Z).
  Notation T := (D + 8 * top)%Z.
  Hypothesis Htop : (0 <= top)%Z.
  Hypothesis Hcnt : (1 <= cnt)%Z.
  Hypothesis H31 : (top + cnt < 2147483648)%Z.
  Hypothesis B47 : (T + 8 * cnt <= 140737488355328)%Z.

  Hypothesis ACT : acc bgbsegs m T (8 * cnt).
  Hypothesis ALD : (D mod 8 = 0)%Z.
  Hypothesis OFFT : offshW [(T, T + 8 * cnt)]%Z.

  Hypothesis UBD : (0 < D)%Z.

  Notation SH pc mm x10 x11 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 D) x13 x14 x15 x16 a7 s2 s3 (Z_to_bv 64 (top + cnt)) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgbsegs)).

  Lemma ALT : (T mod 8 = 0)%Z.
  Proof using ALD. clear - ALD. Z.div_mod_to_equations. lia. Qed.

  Lemma shT : forall m1 i (k : nat) ad, ZINV m T cnt m1 i -> (Z.of_nat k < cnt)%Z -> ad = wa (shad (T + 8 * Z.of_nat k)) ->
    ov_read_bytes bgbsegs m1 ad 1 = Some [z8].
  Proof using ACT ALD OFFT B47 UBD Htop.
    intros m1 i k ad (_ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgbsegs _ m m1 T cnt 0 (Z.of_nat k) _ ACT MU OFFT ALT ltac:(clear - UBD Htop B47; lia)); [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  Notation HEAD mm j x15 x16 :=
    (SH 0x2244b8 mm (Z_to_bv 64 (T + 8 * Z.of_nat j)) (Z_to_bv 64 (top + Z.of_nat j)) (Z_to_bv 64 (T + 8 * Z.of_nat j)) (Z_to_bv 64 1) x15 x16).
  Notation KEXIT :=
    (forall m2 x10 x13 x14 x15 x16,
       limbs_at bgbsegs m2 T (repeat 0%Z (Z.to_nat cnt)) -> mem_inv bgbsegs m2 ->
       munch [(T, T + 8 * cnt)]%Z m m2 -> wmono bgbsegs m m2 ->
       evt bgbsegs POST (SH 0x224504 m2 x10 (Z_to_bv 64 (top + cnt)) x13 x14 x15 x16)).

  Lemma zf_round : forall (j : nat) m1 x15 x16,
    (Z.of_nat j < cnt)%Z -> ZINV m T cnt m1 j ->
    ((Z.of_nat (S j) = cnt)%Z -> KEXIT) ->
    ((Z.of_nat (S j) < cnt)%Z -> forall m2 x15 x16, ZINV m T cnt m2 (S j) -> evt bgbsegs POST (HEAD m2 (S j) x15 x16)) ->
    evt bgbsegs POST (HEAD m1 j x15 x16).
  Proof.
    intros j m1 x15 x16 Hj I KE KL.
    pose proof I as (_ & WT & MI & _).
    pose proof ALT as ALT'.
    assert (BC : (0 < T + 8 * Z.of_nat j /\ T + 8 * Z.of_nat j + 8 <= 140737488355328 /\ D <= T + 8 * Z.of_nat j)%Z) by (clear - UBD Htop B47 Hj; lia).
    assert (BK : (0 <= top + Z.of_nat j < 2147483647)%Z) by (clear - Htop H31 Hj; lia).
    assert (AC8 : ((T + 8 * Z.of_nat j) mod 8 = 0)%Z) by (clear - ALT'; Z.div_mod_to_equations; lia).
    ub.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shT m1 _ j ad I Hj ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    destruct (ZINV_store m T cnt m1 j Hj I) as [SOK I1].
    zstep. try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => gen_mem mx m2 end.
    clear SOK I WT MI. try clear m1.
    do 3 zstep.
    rewrite (bn_swrap32_small (top + Z.of_nat j + 1)) by (clear - BK; lia).
    zstep. if_cases KB; zify_cond KB.
    -
      replace (top + Z.of_nat j + 1)%Z with (top + Z.of_nat (S j))%Z by (clear; lia).
      replace (T + 8 * Z.of_nat j + 8)%Z with (T + 8 * Z.of_nat (S j))%Z by (clear; lia).
      eapply KL; [clear - KB Hj H31 Htop; rewrite ?bn_swrap32_small in KB by lia; lia | exact I1].
    -
      assert (E : (Z.of_nat (S j) = cnt)%Z) by (clear - KB Hj H31 Htop; rewrite ?bn_swrap32_small in KB by lia; lia).
      destruct I1 as (HW & _ & MI2 & MU2 & WM2).
      replace (S j) with (Z.to_nat cnt) in HW by (clear - E; lia).
      replace (top + Z.of_nat j + 1)%Z with (top + cnt)%Z by (clear - E; lia).
      eapply KE; [exact E | exact HW | exact MI2 | exact MU2 | exact WM2].
  Qed.

  Lemma zf_loop : forall (k j : nat) m1 x15 x16,
    (Z.of_nat (S j + k) = cnt)%Z -> ZINV m T cnt m1 j -> KEXIT -> evt bgbsegs POST (HEAD m1 j x15 x16).
  Proof.
    induction k as [|k IH]; intros j m1 x15 x16 Hk I K.
    - eapply zf_round; [clear - Hk; lia | exact I | intros _; exact K | intros C; exfalso; clear - C Hk; lia].
    - eapply zf_round; [clear - Hk; lia | exact I | intros C; exfalso; clear - C Hk; lia | ].
      intros _ m2 y15 y16 I2. eapply IH; [clear - Hk; lia | exact I2 | exact K].
  Qed.

  Lemma zfill_blockB : forall x10 x14 x15 x16,
    wr_at bgbsegs m T (8 * cnt) -> mem_inv bgbsegs m ->
    KEXIT ->
    evt bgbsegs POST (SH 0x2244b0 m x10 (Z_to_bv 64 top) (Z_to_bv 64 T) x14 x15 x16).
  Proof.
    intros x10 x14 x15 x16 WT MI K.
    assert (I0 : ZINV m T cnt m 0).
    { unfold ZINV. cbn [repeat]. split; [apply limbs_at_nil; clear - UBD Htop B47 Hcnt; lia|].
      split; [exact WT|]. split; [exact MI|]. split; [apply munch_refl | apply wmono_refl]. }
    ub. zstep.
    setreg 14%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; replace (0 <? D)%Z with true by (symmetry; apply Z.ltb_lt; exact UBD); reflexivity).
    eapply evt_eq; [ | eapply (zf_loop (Z.to_nat cnt - 1) 0 m x15 x16); [clear - Hcnt; lia | exact I0 | exact K] ].
    replace (8 * Z.of_nat 0)%Z with 0%Z by (clear; lia). rewrite !Z.add_0_r. reflexivity.
  Qed.
End Block.
