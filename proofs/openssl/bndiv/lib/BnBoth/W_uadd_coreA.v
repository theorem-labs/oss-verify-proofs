(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnModel BnAddSpec BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require W_uadd_core.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import BnRepDefs AsStruct BnCallsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2437992 => 2
  | 2438004 => 1
  | 2438008 => 2
  | 2438012 => 2
  | 2438016 => 1
  | 2438020 => 2
  | 2438156 => 1
  | 2438160 => 2
  | 2438168 => 2
  | 2438184 => 2
  | 2438188 => 1
  | 2438192 => 2
  | 2438308 => 1
  | 2438312 => 1
  | 2438316 => 2
  | 2438320 => 1
  | 2438324 => 1
  | 2438328 => 1
  | 2438332 => 1
  | 2438336 => 2
  | 2438344 => 1
  | 2438348 => 1
  | 2438352 => 2
  | 2438356 => 1
  | 2438360 => 1
  | 2438364 => 1
  | 2438368 => 2
  | 2438380 => 1
  | 2438384 => 1
  | 2438408 => 1
  | 2438420 => 1
  | 2438428 => 2
  | 2438436 => 1
  | 2438440 => 2
  | 2438448 => 2
  | 2438452 => 2
  | 2438468 => 1
  | 2438472 => 2
  | 2438480 => 2
  | 2438484 => 2
  | 2438548 => 2
  | 2438552 => 1
  | 2438556 => 2
  | 2438600 => 1
  | 2438604 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Notation uadd_lists := W_uadd_core.uadd_lists.
Notation uadd_top := W_uadd_core.uadd_top.
Notation uadd_buf := W_uadd_core.uadd_buf.
Notation uadd_bn := W_uadd_core.uadd_bn.

(* [comment removed for export] *)
Ltac store_bundleA I2 :=
  unfold wa in I2;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad ?bs) _) =>
      let m' := fresh "m" in
      gen_mem (write_to_mem m ad bs) m';
      repeat match goal with H : context [m] |- _ => clear H end; try clear m
  end.

Section Core.
  (* [comment removed for export] *)
  Variables (ra0 sp gp tp s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (jb : list byte).
  (* [comment removed for export] *)
  Variables (m1 : word -> option byte) (lo R A B Dr Da Db : Z) (br : bignum bptr) (la lb : list Z).
  Notation SP := (bv_unsigned sp).
  Notation max := (length la).
  Notation min := (length lb).
  Notation mx := (Z.of_nat (length la)).
  Notation mn := (Z.of_nat (length lb)).
  Notation dmx := (Z.of_nat (bn_dmax br)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -96)).

  (* [comment removed for export] *)
  Definition uadd_preA : Prop :=
    limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max + 1 <= bn_dmax br)%nat /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * mx <= lo /\ 0 <= Db /\ Db + 8 * mn <= lo /\ lo <= SP - 208 /\ SP <= 140737488355328)%Z /\
    (* [comment removed for export] *)
    (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z /\
    (* [comment removed for export] *)
    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z /\
    (* [comment removed for export] *)
    (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z /\
    (* [comment removed for export] *)
    (R mod 8 = 0 /\ A mod 8 = 0 /\ B mod 8 = 0 /\ Dr mod 8 = 0 /\ Da mod 8 = 0 /\ Db mod 8 = 0)%Z /\
    ((R + 24 <= SHLO \/ SHHI <= R) /\ (Dr + 8 * dmx <= SHLO \/ SHHI <= Dr) /\ SHHI <= lo /\ (R + 24 <= 65536 \/ 12570624 <= R))%Z.
  Hypothesis PRE : uadd_preA.
  Definition uadd_upreA : Prop := ub_ptr_ok mx Dr /\ ub_ptr_ok mx Da /\ ub_ptr_ok mn Db.
  Hypothesis UPRE : uadd_upreA.

  Lemma P_lists : limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max + 1 <= bn_dmax br)%nat.
  Proof. destruct PRE as (H1 & H2 & H3 & H4 & H5 & _). auto. Qed.
  Lemma P_rng : (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * mx <= lo /\ 0 <= Db /\ Db + 8 * mn <= lo /\ lo <= SP - 208 /\ SP <= 140737488355328)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_lo : (lo <= SP - 208 /\ SP < 18446744073709551616)%Z.
  Proof. pose proof P_rng as H. lia. Qed.
  Lemma P_structs : (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & H1 & H2 & _). auto. Qed.
  Lemma P_sarr : (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _). auto. Qed.
  Lemma P_alias : (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). auto. Qed.
  Lemma P_al : (R mod 8 = 0 /\ A mod 8 = 0 /\ B mod 8 = 0 /\ Dr mod 8 = 0 /\ Da mod 8 = 0 /\ Db mod 8 = 0)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_sh : ((R + 24 <= SHLO \/ SHHI <= R) /\ (Dr + 8 * dmx <= SHLO \/ SHHI <= Dr) /\ SHHI <= lo /\ (R + 24 <= 65536 \/ 12570624 <= R))%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  Notation Wfin := [(Dr, Dr + 8 * (mx + 1)); (R, R + 24); (SP - 208, SP)]%Z.
  Notation FRAME := [CB 8 jb; C8 s9_; C8 s8_; C8 s7_; C8 s6_; C8 s5_; C8 s4_; C8 s3_; C8 s2_; C8 s1_; C8 s0_; C8 ra0].

  Lemma P_off : offshW Wfin.
  Proof.
    pose proof P_sh as (H1 & H2 & H3 & _). pose proof P_rng as RNG. pose proof P_lists as (_ & _ & _ & _ & HD).
    cbn [offshW]. unfold SHLO, SHHI in *. repeat split; lia.
  Qed.

  Definition uadd_postA : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m2,
      ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0_ s1_ (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10 s11 t3 t4 t5 t6)
               F (ret_pc ra0) fc None m2 (seg_rom bsegs)
      /\ munch Wfin m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2
      /\ rw_cells bsegs m2 R (bn_cells Dr (uadd_bn br la lb)) /\ u64arr bsegs m2 Dr (wlimbs (uadd_buf br la lb))
      /\ stk bsegs m2 lo SP.

  (* [comment removed for export] *)
  Notation ST pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma ua_epi : forall m2 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6,
    rw_cells bsegs m2 (SP + -96) FRAME -> stk bsegs m2 lo (SP + -96) -> mem_inv bsegs m2 ->
    munch Wfin m1 m2 -> wmono bsegs m1 m2 ->
    rw_cells bsegs m2 R (bn_cells Dr (uadd_bn br la lb)) -> u64arr bsegs m2 Dr (wlimbs (uadd_buf br la lb)) ->
    evt bsegs uadd_postA (ST 0x2535f8 m2 x1 t0 t1 t2 x8 x9 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6).
  Proof.
    intros m2 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 t3 t4 t5 t6 FR ST MI MU WM SR UR.
    unfold bn_cells in SR.
    do 11 (ub; zstep).
    pose proof P_lo as PLO.
    release_frame FR ST (bv_unsigned sp). ub; zstep. ub; zstep.
    apply evt_done. unfold uadd_postA. do 14 eexists. exists m2. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [unfold bn_cells; exact SR|]. split; [exact UR | exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition core_memA : Prop :=
    rw_cells bsegs m1 R (bn_cells Dr br) /\ u64arr bsegs m1 Dr (wlimbs (bn_buf br)) /\
    rw_cells bsegs m1 A [C8 (wz Da)] /\ rw_cells bsegs m1 B [C8 (wz Db)] /\
    limbs_at bsegs m1 Da la /\ limbs_at bsegs m1 Db lb /\
    rw_cells bsegs m1 (SP + -96) FRAME /\ stk bsegs m1 lo (SP + -96) /\ mem_inv bsegs m1 /\
    shb_cells bsegs 6163672 6961656 m1 /\
    acc bsegs m1 R 24 /\ acc bsegs m1 A 8 /\ acc bsegs m1 B 8 /\
    acc bsegs m1 Dr (8 * dmx) /\ acc bsegs m1 Da (8 * mx) /\ acc bsegs m1 Db (8 * mn).
  Hypothesis MEM : core_memA.

  Lemma M_acc : acc bsegs m1 R 24 /\ acc bsegs m1 A 8 /\ acc bsegs m1 B 8 /\
    acc bsegs m1 Dr (8 * dmx) /\ acc bsegs m1 Da (8 * mx) /\ acc bsegs m1 Db (8 * mn).
  Proof. destruct MEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  (* [comment removed for export] *)
  Definition UB (m2 : word -> option byte) (pre l : list Z) (topv negv : word) : Prop :=
    rw_cells bsegs m2 R [C8 (wz Dr); C4 topv; C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] /\
    limbs_at bsegs m2 Dr pre /\ wr_at bsegs m2 Dr (8 * dmx) /\
    limbs_at bsegs m2 (Da + 8 * Z.of_nat (length pre)) l /\
    rw_cells bsegs m2 (SP + -96) FRAME /\ stk bsegs m2 lo (SP + -96) /\ mem_inv bsegs m2 /\
    munch Wfin m1 m2 /\ wmono bsegs m1 m2.

  (* [comment removed for export] *)
  Lemma UB_store : forall m2 pre x l topv negv v,
    UB m2 pre (x :: l) topv negv -> (length pre + S (length l) <= max)%nat ->
    store_ok bsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true /\
    UB (write_to_mem m2 (wa (Dr + 8 * Z.of_nat (length pre))) (le8 (Z_to_bv 64 v))) (pre ++ [v]) l topv negv.
  Proof.
    intros m2 pre x l topv negv v (SR & HP & HW & HL & FR & ST & MI & MU & WM) Hlen.
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). pose proof P_alias as (AL & _).
    pose proof (limbs_at_bound _ _ _ _ HL) as BL. cbn [length] in BL.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    change (2^64)%Z with 18446744073709551616%Z in *.
    assert (SOK : store_ok bsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true).
    { apply (wr_at_store_ok bsegs m2 Dr (8 * dmx)); [exact HW | lia | lia]. }
    split; [exact SOK|]. unfold UB.
    split. { apply rw_cells_frame; [exact SR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add]; lia]. }
    split. { apply limbs_at_snoc_write; [exact HP | change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply wr_at_write. exact HW. }
    split. { rewrite length_app. cbn [length]. replace (Da + 8 * Z.of_nat (length pre + 1))%Z with (Da + 8 * Z.of_nat (length pre) + 8)%Z by lia.
             apply limbs_at_write_other; [eapply limbs_at_cons_inv; exact HL | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia | rewrite L8; lia]. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add length]; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma UB_store_last : forall m2 pre topv negv v,
    UB m2 pre [] topv negv -> length pre = max ->
    store_ok bsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true /\
    UB (write_to_mem m2 (wa (Dr + 8 * Z.of_nat (length pre))) (le8 (Z_to_bv 64 v))) (pre ++ [v]) [] topv negv.
  Proof.
    intros m2 pre topv negv v (SR & HP & HW & HL & FR & ST & MI & MU & WM) Hlen.
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _).
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    change (2^64)%Z with 18446744073709551616%Z in *.
    assert (SOK : store_ok bsegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true).
    { apply (wr_at_store_ok bsegs m2 Dr (8 * dmx)); [exact HW | lia | lia]. }
    split; [exact SOK|]. unfold UB.
    split. { apply rw_cells_frame; [exact SR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add]; lia]. }
    split. { apply limbs_at_snoc_write; [exact HP | change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply wr_at_write. exact HW. }
    split. { apply limbs_at_nil. change (2^64)%Z with 18446744073709551616%Z. rewrite length_app. cbn [length]. lia. }
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add length]; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; change (2^64)%Z with 18446744073709551616%Z; lia | rewrite L8; cbn [inside]; left; lia]. }
    apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma ua_final_arr : forall m2 w, munch Wfin m1 m2 -> wmono bsegs m1 m2 -> limbs_at bsegs m2 Dr w -> length w = (max + 1)%nat ->
    u64arr bsegs m2 Dr (wlimbs (splice (bn_buf br) 0 w)).
  Proof.
    intros m2 w MU WM HWL Hlen.
    destruct MEM as (_ & UR1 & _).
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _).
    unfold bn_dmax in *.
    apply (limbarr_limbs_at bsegs) in UR1. destruct UR1 as [HL1 HW1].
    assert (LS : length (splice (bn_buf br) 0 w) = length (bn_buf br)) by (apply splice_length; lia).
    apply u64arr_of_limbs_at.
    - replace Dr with (Dr + 8 * Z.of_nat 0)%Z in HWL by lia.
      replace Dr with (Dr + 8 * Z.of_nat 0)%Z at 1 by lia. rewrite Z.add_0_r.
      eapply (limbs_at_splice bsegs Wfin m1 m2 Dr (bn_buf br) 0 w HL1 MU); [lia | exact HWL | |].
      + cbn [disjoint_from]. lia.
      + cbn [disjoint_from]. lia.
    - rewrite LS. eapply wr_at_transport; [exact HW1 | exact WM].
  Qed.

  (* [comment removed for export] *)
  Ltac shrd ACC MU p n k AL BD :=
    let ad := cur_mem_addr in let RD := fresh "RDsh" in
    pose proof (acc_rd_limb bsegs _ m1 _ p n 0 k ad ACC MU P_off AL BD eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(sh_addr_k)) as RD;
    ub; zstep; clear RD.

  (* [comment removed for export] *)
  Lemma ua_neg : forall m2 negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x24 x25 t3 t4 t5 t6,
    rw_cells bsegs m2 R [C8 (wz Dr); C4 (wz (Z.of_nat (uadd_top la lb))); C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] ->
    u64arr bsegs m2 Dr (wlimbs (uadd_buf br la lb)) -> length (uadd_buf br la lb) = bn_dmax br ->
    rw_cells bsegs m2 (SP + -96) FRAME -> stk bsegs m2 lo (SP + -96) -> mem_inv bsegs m2 ->
    munch Wfin m1 m2 -> wmono bsegs m1 m2 ->
    evt bsegs uadd_postA (ST 0x2535dc m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 (Z_to_bv 64 SHB) x23 x24 x25 t3 t4 t5 t6).
  Proof.
    intros m2 negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x24 x25 t3 t4 t5 t6 SR UR LU FR ST MI MU WM.
    pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). pose proof P_al as (ALR & _). pose proof M_acc as (ACR & _).
    assert (LW : length (wlimbs (uadd_buf br la lb)) = bn_dmax br) by (rewrite wlimbs_len; exact LU).
    assert (BR : (0 <= R /\ R + 8 * 3 <= 140737488355328)%Z) by (clear - RNG; lia).
    do 3 (ub; zstep).
    shrd ACR MU R 3%Z 2%Z ALR BR. ub; chk0.
    ub; step. ub; zstep.
    eapply ua_epi; try eassumption.
    unfold bn_cells, W_uadd_core.uadd_bn, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite LU. exact SR.
  Qed.

  (* [comment removed for export] *)
  Lemma ua_fin : forall m2 negv x1 t0 t1 t2 x8 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 t3 t4 t5 t6,
    (0 < max)%nat ->
    UB m2 (fst (uadd_lists la lb)) [] (wz mx) negv ->
    evt bsegs uadd_postA (ST 0x253594 m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 (snd (uadd_lists la lb))) (Z_to_bv 64 (Dr + 8 * mx))
                            a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (R + 8)) x19 x20 x21 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad (R + 8))) x24 x25 t3 t4 t5 t6).
  Proof.
    intros m2 negv x1 t0 t1 t2 x8 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 t3 t4 t5 t6 Hmax I.
    pose proof P_lists as (LLA & LLB & HMM & OKR & HD).
    pose proof (W_uadd_core.uadd_lists_facts la lb LLA LLB HMM) as (LW & NW & CW).
    destruct (UB_store_last m2 _ _ _ (snd (uadd_lists la lb)) I NW) as [SOK I2]. rewrite NW in SOK, I2.
    pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). pose proof P_al as (ALR & _ & _ & ALDR & _).
    pose proof M_acc as (ACR & _ & _ & ACDR & _).
    assert (BR : (0 <= R /\ R + 8 * 3 <= 140737488355328)%Z) by (clear - RNG; lia).
    assert (BDR : (0 <= Dr /\ Dr + 8 * dmx <= 140737488355328)%Z) by (clear - RNG; lia).
    pose proof I as (SR0 & _ & _ & _ & _ & _ & _ & MU0 & _).
    destruct OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    do 2 (ub; zstep).
    shrd ACDR MU0 Dr (Z.of_nat (bn_dmax br)) (Z.of_nat (length la)) ALDR BDR. ub; chk0.
    clear SR0 MU0.
    ub; zstep. store_bundleA I2.
    destruct I2 as (SR & HP & HW & _ & FR & ST & MI & MU & WM).
    shrd ACR MU R 3%Z 1%Z ALR BR. ub; chk0.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    ub; zstep. unfold wz at 1. rewrite (sx32_small mx) by (clear - HD DMR; lia).
    zstep. rewrite (bn_swrap32_small (snd (uadd_lists la lb) + 0)) by (clear - CW; lia). rewrite Z.add_0_r.
    zstep. ub.
    shrd ACR MU R 3%Z 1%Z ALR BR. chk0.
    step.
    apply (limbs_at_transport bsegs [(R, R + 24)]%Z m m0) in HP;
      [| exact MUt | cbn [disjoint_from]; rewrite length_app, NW; cbn [length]; clear - SA1 HD; lia].
    clear MUt.
    assert (ETOP : uadd_top la lb = (max + Z.to_nat (snd (uadd_lists la lb)))%nat).
    { unfold W_uadd_core.uadd_top. destruct (Nat.eqb_spec max 0) as [E0|_]; [exfalso; clear - E0 Hmax; lia | reflexivity]. }
    assert (EBUF : uadd_buf br la lb = splice (bn_buf br) 0 (fst (uadd_lists la lb) ++ [snd (uadd_lists la lb)])).
    { unfold W_uadd_core.uadd_buf. destruct (Nat.eqb_spec max 0) as [E0|_]; [exfalso; clear - E0 Hmax; lia | reflexivity]. }
    assert (LWW : length (fst (uadd_lists la lb) ++ [snd (uadd_lists la lb)]) = (max + 1)%nat) by (rewrite length_app, NW; reflexivity).
    eapply (ua_neg m0 negv); [ | | | exact FR | exact ST | exact MI | exact MU | exact WM].
    - rewrite ETOP. unfold wz at 2. rewrite Nat2Z.inj_add, Z2Nat.id by (clear - CW; lia). exact SR.
    - rewrite EBUF. apply ua_final_arr; [exact MU | exact WM | exact HP | exact LWW].
    - rewrite EBUF. apply splice_length. rewrite LWW. clear - HD. unfold bn_dmax in *. lia.
  Qed.

  Lemma shad_next : forall p, (p mod 8 = 0)%Z -> (shad p + 1 = shad (p + 8))%Z.
  Proof. intros p Hp. unfold shad. clear - Hp. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma ua_loop : forall l pre c m2 negv x1 t2 x8 a1 x21 x25 t3 t4 t5 t6,
    UB m2 pre l (Z_to_bv 64 mx) negv -> l <> [] -> (length pre + length l = max)%nat -> limbs l -> (0 <= c <= 1)%Z ->
    fst (uadd_lists la lb) = pre ++ fst (add_carry_words l c) -> snd (uadd_lists la lb) = snd (add_carry_words l c) ->
    evt bsegs uadd_postA
      (ST 0x253514 m2 x1 (Z_to_bv 64 (Da + 8 * (Z.of_nat (length pre) - mn))) (Z_to_bv 64 (Dr + 8 * (Z.of_nat (length pre) - mn))) t2 x8
          (Z_to_bv 64 R) (Z_to_bv 64 c) a1 (Z_to_bv 64 (8 * mn)) (Z_to_bv 64 0) (Z_to_bv 64 0)
          (Z_to_bv 64 (shad (Da + 8 * Z.of_nat (length pre)))) (Z_to_bv 64 (shad (Dr + 8 * Z.of_nat (length pre)))) (Z_to_bv 64 9)
          (Z_to_bv 64 (R + 8)) (Z_to_bv 64 (Da + 8 * (Z.of_nat (length pre) - mn))) (Z_to_bv 64 (Dr + 8 * (Z.of_nat (length pre) - mn))) x21
          (Z_to_bv 64 SHB) (Z_to_bv 64 (shad (R + 8))) (Z_to_bv 64 (Z.of_nat (length l))) x25 t3 t4 t5 t6).
  Proof.
    induction l as [|x l IH]; intros pre c m2 negv x1 t2 x8 a1 x21 x25 t3 t4 t5 t6 I NE HLEN LL HC E1 E2;
      [exfalso; apply NE; reflexivity|]. clear NE.
    pose proof P_lists as (_ & _ & HMM & OKR & HD). pose proof OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    pose proof P_rng as RNG. pose proof P_al as (_ & _ & _ & ALDR & ALDA & _).
    pose proof M_acc as (_ & _ & _ & ACDR & ACDA & _).
    assert (BDR : (0 <= Dr /\ Dr + 8 * dmx <= 140737488355328)%Z) by (clear - RNG; lia).
    assert (BDA : (0 <= Da /\ Da + 8 * mx <= 140737488355328)%Z) by (clear - RNG; lia).
    cbn [length] in HLEN.
    pose proof UPRE as (UBR & UBA & _).
    destruct (UBR ltac:(clear - HLEN; lia)) as [PR _]. destruct (UBA ltac:(clear - HLEN; lia)) as [PA _].
    apply limbs_cons_lit in LL. destruct LL as [RX LL].
    pose proof I as (_ & _ & _ & HL & _ & _ & _ & MU0 & _).
    assert (HK : (Z.of_nat (length pre) + 1 + Z.of_nat (length l) = mx)%Z) by (clear - HLEN; lia).

    ub. zstep.
    setreg 24%Z (Z_to_bv 64 (Z.of_nat (length l)))
      ltac:(f_equal; cbn [length]; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia;
            change (2^64)%Z with 18446744073709551616%Z; rewrite bn_swrap32_mod by (clear - HK HD DMR; lia); clear; lia).
    setreg 11%Z (Z_to_bv 64 (Z.of_nat (length l) + 1))
      ltac:(f_equal; cbn [length]; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia;
            change (2^64)%Z with 18446744073709551616%Z; rewrite bn_swrap32_mod by (clear - HK HD DMR; lia); clear; lia).
    ub.

    zstep. setreg 11%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (length pre))) ltac:(f_equal; clear; lia).
    ub. zstep. setreg 7%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (length pre))) ltac:(f_equal; clear; lia).
    ub.
    shrd ACDA MU0 Da (Z.of_nat (length la)) (Z.of_nat (length pre)) ALDA BDA. chk0.

    zstep. setreg 11%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (length pre))) ltac:(f_equal; clear; lia).
    ub. zstep. setreg 28%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (length pre))) ltac:(f_equal; clear; lia).
    ub.
    shrd ACDR MU0 Dr (Z.of_nat (bn_dmax br)) (Z.of_nat (length pre)) ALDR BDR. chk0.
    clear MU0.

    (let ad := cur_mem_addr in pose proof (limbs_at_read_hd bsegs m2 _ x l ad HL ltac:(unfold wa; reflexivity)) as RD); zstep; clear RD.
    do 5 zstep.
    zstep. setreg 11%Z (Z_to_bv 64 (addw x c)) ltac:(unfold addw; apply Z_to_bv_eqm; rewrite BW_lit; clear; Z.div_mod_to_equations; lia).
    destruct (UB_store m2 pre x l _ negv (addw x c) I ltac:(clear - HLEN; lia)) as [SOK I2].
    assert (RT : (0 <= addw x c < 18446744073709551616)%Z) by (unfold addw; rewrite BW_lit; apply Z.mod_pos_bound; clear; lia).
    zstep. store_bundleA I2.
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 (if addw x c =? 0 then c else 0)%Z)
      ltac:(f_equal; clear - HC RT; destruct (Z.eqb_spec (addw x c) 0) as [E0|N0];
            [rewrite E0; cbn [Z.ltb Z.compare Z.b2z]; assert (c = 0 \/ c = 1)%Z as [->| ->] by lia; reflexivity
            |replace (addw x c <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity]).
    assert (E1' : fst (uadd_lists la lb) = (pre ++ [addw x c]) ++ fst (add_carry_words l (if addw x c =? 0 then c else 0)%Z)).
    { rewrite E1, W_uadd_core.add_carry_words_cons. cbn [fst]. rewrite <- app_assoc. reflexivity. }
    assert (E2' : snd (uadd_lists la lb) = snd (add_carry_words l (if addw x c =? 0 then c else 0)%Z)).
    { rewrite E2, W_uadd_core.add_carry_words_cons. reflexivity. }
    assert (HC' : (0 <= (if addw x c =? 0 then c else 0) <= 1)%Z) by (clear - HC; destruct (addw x c =? 0)%Z; lia).
    assert (LP : length (pre ++ [addw x c]) = (length pre + 1)%nat) by (rewrite length_app; reflexivity).
    setreg 5%Z (Z_to_bv 64 (Da + 8 * (Z.of_nat (length (pre ++ [addw x c])) - mn))) ltac:(f_equal; rewrite LP; clear; lia).
    setreg 6%Z (Z_to_bv 64 (Dr + 8 * (Z.of_nat (length (pre ++ [addw x c])) - mn))) ltac:(f_equal; rewrite LP; clear; lia).
    setreg 19%Z (Z_to_bv 64 (Da + 8 * (Z.of_nat (length (pre ++ [addw x c])) - mn))) ltac:(f_equal; rewrite LP; clear; lia).
    setreg 20%Z (Z_to_bv 64 (Dr + 8 * (Z.of_nat (length (pre ++ [addw x c])) - mn))) ltac:(f_equal; rewrite LP; clear; lia).
    setreg 15%Z (Z_to_bv 64 (shad (Da + 8 * Z.of_nat (length (pre ++ [addw x c])))))
      ltac:(f_equal; rewrite LP, shad_next by (clear - ALDA; Z.div_mod_to_equations; lia); f_equal; clear; lia).
    setreg 16%Z (Z_to_bv 64 (shad (Dr + 8 * Z.of_nat (length (pre ++ [addw x c])))))
      ltac:(f_equal; rewrite LP, shad_next by (clear - ALDR; Z.div_mod_to_equations; lia); f_equal; clear; lia).
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (NE : l <> []) by (intros ->; apply KZ; reflexivity).
      eapply IH; [exact I2 | exact NE | rewrite LP; clear - HLEN; lia | exact LL | exact HC' | exact E1' | exact E2'].
    - (* [comment removed for export] *)
      assert (EL : l = []) by (clear - KZ; destruct l; [reflexivity | cbn [length] in KZ; lia]). subst l.
      cbn [add_carry_words fst snd] in E1', E2'. rewrite app_nil_r in E1'.
      zstep.
      setreg 11%Z (Z_to_bv 64 (Dr + 8 * mx)) ltac:(f_equal; rewrite LP; clear - HLEN; cbn [length] in HLEN; lia).
      rewrite <- E2'. rewrite <- E1' in I2.
      eapply ua_fin; [clear - HLEN; lia | exact I2].
  Qed.

  (* [comment removed for export] *)
  Lemma uadd_coreA : forall x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x23 t3 t4 t5 t6,
    evt bsegs uadd_postA
      (ST 0x253424 m1 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 R) a1 a2 a3 a4 a5 a6 a7
          x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 mn) (Z_to_bv 64 SHB) x23 (Z_to_bv 64 (mx - mn)) (Z_to_bv 64 mx) t3 t4 t5 t6).
  Proof.
    intros x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x23 t3 t4 t5 t6.
    pose proof UPRE as (UBR & UBA & UBB).
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & FR & ST & MI & (SHB1 & SHB2) & ACR & ACA & ACB & ACDR & ACDA & ACDB).
    pose proof P_lists as (LLA & LLB & HMM & OKR & HD).
    pose proof P_rng as RNG. pose proof P_al as (ALR & ALA & ALB & ALDR & ALDA & ALDB). pose proof P_sh as (SHR & SHDR & SHLOlo & RIMG).
    pose proof OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    pose proof (munch_refl Wfin m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    pose proof (munch_refl [(R, R + 24)]%Z m1) as MUt.
    assert (BR : (0 <= R /\ R + 8 * 3 <= 140737488355328)%Z) by (clear - RNG; lia).
    assert (BA : (0 <= A /\ A + 8 * 1 <= 140737488355328)%Z) by (clear - RNG; lia).
    assert (BB : (0 <= B /\ B + 8 * 1 <= 140737488355328)%Z) by (clear - RNG; lia).
    unfold bn_cells in SR.
    ub; zstep. if_cases K; zify_cond K; [exfalso; clear - K RNG; lia|]. clear K.
    pose proof P_structs as (SAR & SBR). pose proof P_sarr as (SA1 & SA2 & SA3).
    assert (LWR : length (wlimbs (bn_buf br)) = bn_dmax br) by (apply wlimbs_len).
    do 3 (ub; zstep).
    shrd ACR MU R 3%Z 1%Z ALR BR. ub; chk0.
    ub; step.
    ub; zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (E0 : max = 0%nat) by (clear - K0; lia).
      assert (ETOP : uadd_top la lb = 0%nat) by (unfold W_uadd_core.uadd_top; rewrite E0; reflexivity).
      assert (EBUF : uadd_buf br la lb = bn_buf br) by (unfold W_uadd_core.uadd_buf; rewrite E0; reflexivity).
      eapply (ua_neg m); [ | | | exact FR | exact ST | exact MI | exact MU | exact WM].
      - rewrite ETOP. rewrite E0 in SR. exact SR.
      - rewrite EBUF. exact UR.
      - rewrite EBUF. reflexivity. }
    assert (Hmax : (0 < max)%nat) by (clear - K0; lia). clear K0.
    assert (Hmax' : (0 < mx)%Z) by (clear - Hmax; lia).
    do 2 (ub; zstep). shrd ACA MU A 1%Z 0%Z ALA BA. ub; chk0.
    do 2 (ub; zstep). shrd ACB MU B 1%Z 0%Z ALB BB. ub; chk0.
    do 2 (ub; zstep). shrd ACR MU R 3%Z 0%Z ALR BR. ub; chk0.
    do 3 (ub; zstep). do 3 (ub; zstep).
    (* [comment removed for export] *)
    pose proof P_alias as (ALIA & ALIB).
    assert (HLAm : limbs_at bsegs m Da la).
    { eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]. }
    assert (HLBm : limbs_at bsegs m Db lb).
    { eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]. }
    assert (OFFt : offshW [(R, R + 24)]%Z) by (cbn [offshW]; clear - SHR; lia).
    assert (ACDRm : acc bsegs m Dr (8 * dmx)) by (eapply (acc_munch bsegs _ m1 m Dr _ ACDR MUt OFFt); clear - RNG; lia).
    assert (ACDAm : acc bsegs m Da (8 * mx)) by (eapply (acc_munch bsegs _ m1 m Da _ ACDA MUt OFFt); clear - RNG; lia).
    assert (ACDBm : acc bsegs m Db (8 * mn)) by (eapply (acc_munch bsegs _ m1 m Db _ ACDB MUt OFFt); clear - RNG; lia).
    clear HLA HLB MUt.
    assert (HW : wr_at bsegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bsegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    assert (LF : length (firstn min la) = min) by (apply firstn_length_le; exact HMM).
    assert (ESPF : bv_unsigned SPF = (SP + -96)%Z) by (apply unsigned_lit; clear - RNG; lia).
    ub; zstep.
    eapply (call_add_wordsA uadd_postA) with (a := firstn min la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -96)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | split; [exact SHB1 | exact SHB2]
      | apply limbs_firstn; exact LLA | exact LLB | rewrite LF; reflexivity | rewrite LF; clear - HMM HD DMR; lia
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | rewrite LF; apply unsigned_lit; clear - HMM HD DMR; lia
      | apply (limbs_at_firstn bsegs); exact HLAm | exact HLBm
      | rewrite LF; replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HMM HD; lia]
      | rewrite LF; unfold alias_ok; clear - ALIA HMM HD; lia | rewrite LF; unfold alias_ok; clear - ALIB HMM HD; lia
      | clear - RNG; lia | rewrite LF; clear - RNG HMM HD; lia | rewrite LF; clear - RNG HMM; lia | rewrite LF; clear - RNG; lia
      | rewrite LF; eapply acc_sub; [exact ACDRm | lia | clear - HMM HD; lia]
      | rewrite LF; eapply acc_sub; [exact ACDAm | lia | clear - HMM; lia]
      | rewrite LF; exact ACDBm
      | rewrite LF; unfold aptrs3; clear - ALDR ALDA ALDB SHDR SHLOlo HMM HD; lia
      | rewrite LF; intros Hn; apply UBR; clear - Hn HMM; lia | rewrite LF; intros Hn; apply UBA; clear - Hn HMM; lia | rewrite LF; exact UBB | ].
    rewrite LF. intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.
    (* [comment removed for export] *)
    pose proof (add_words_spec (firstn min la) lb (limbs_firstn _ _ LLA) LLB LF) as AWS.
    assert (ELS : uadd_lists la lb = (fst (add_words (firstn min la) lb) ++ fst (add_carry_words (skipn min la) (snd (add_words (firstn min la) lb))),
                                      snd (add_carry_words (skipn min la) (snd (add_words (firstn min la) lb))))).
    { unfold W_uadd_core.uadd_lists. destruct (add_words (firstn min la) lb) as [sv cv]. cbn [fst snd]. destruct (add_carry_words (skipn min la) cv). reflexivity. }
    destruct (add_words (firstn min la) lb) as [sv cv]. cbn [fst snd] in *. destruct AWS as (LSV & NSV & CV & _). rewrite LF in NSV.
    assert (HL2 : limbs_at bsegs m2 (Da + 8 * Z.of_nat (length sv)) (skipn min la)).
    { rewrite NSV. eapply limbs_at_transport; [apply (limbs_at_skipn bsegs); [exact HLAm | exact HMM] | exact MUc |].
      cbn [disjoint_from]. rewrite length_skipn. clear - ALIA RNG HMM HD. lia. }
    assert (I : UB m2 sv (skipn min la) (Z_to_bv 64 mx) (wz (Z.b2z (bn_neg br)))).
    { unfold UB. split.
      { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 RNG HMM HD; lia]. }
      split; [exact HRc|]. split; [eapply wr_at_transport; [exact HW | exact WMc]|]. split; [exact HL2|].
      split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn; clear - RNG HMM HD; lia]. }
      split; [exact STc|]. split; [exact MIc|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HMM. lia. }
      eapply wmono_trans; [exact WM | exact WMc]. }
    clear SR UR HAd HBd FR ST MI MU WM HLAm HLBm HW MUc WMc MIc HRc STc HL2 ACDRm ACDAm ACDBm SHB1 SHB2 m.
    setreg 23%Z (Z_to_bv 64 (shad (R + 8))) ltac:(f_equal; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).

    destruct (UBR Hmax') as [PR _]. destruct (UBA Hmax') as [PA _].
    zstep. replace (Z.shiftl mn 3) with (8 * mn)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    ub.
    zstep. setreg 15%Z (Z_to_bv 64 (Da + 8 * mn)) ltac:(f_equal; clear; lia).
    ub.
    zstep. rewrite (bn_swrap32_small (mx - mn + 0)) by (clear - HMM HD DMR; lia). rewrite Z.add_0_r.
    assert (LSK : length (skipn min la) = (max - min)%nat) by apply length_skipn.
    zstep. if_cases KD; zify_cond KD.
    { (* [comment removed for export] *)
      assert (ESK : skipn min la = []) by (clear - KD LSK; destruct (skipn min la); [reflexivity | cbn [length] in LSK; lia]).
      rewrite ESK in ELS, I. cbn [add_carry_words fst snd] in ELS. rewrite app_nil_r in ELS.
      setreg 11%Z (Z_to_bv 64 (Dr + 8 * mx)) ltac:(f_equal; clear - KD; lia).
      replace (Z_to_bv 64 cv) with (Z_to_bv 64 (snd (uadd_lists la lb))) by (rewrite ELS; reflexivity).
      eapply ua_fin; [exact Hmax | rewrite ELS; exact I]. }

    ub. unfold wz.
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7_wrap; exact ALDA).
    setreg 14%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7_wrap; exact ALDR).
    zstep. do 4 zstep.
    setreg 15%Z (Z_to_bv 64 (shad (Da + 8 * Z.of_nat (length sv))))
      ltac:(f_equal; unfold shad; rewrite NSV, Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 16%Z (Z_to_bv 64 (shad (Dr + 8 * Z.of_nat (length sv))))
      ltac:(f_equal; unfold shad; rewrite NSV, Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; clear; lia).
    ub. do 2 zstep.
    setreg 5%Z (Z_to_bv 64 (Da + 8 * (Z.of_nat (length sv) - mn))) ltac:(f_equal; rewrite NSV; clear; lia).
    setreg 6%Z (Z_to_bv 64 (Dr + 8 * (Z.of_nat (length sv) - mn))) ltac:(f_equal; rewrite NSV; clear; lia).
    setreg 19%Z (Z_to_bv 64 (Da + 8 * (Z.of_nat (length sv) - mn))) ltac:(f_equal; rewrite NSV; clear; lia).
    setreg 20%Z (Z_to_bv 64 (Dr + 8 * (Z.of_nat (length sv) - mn))) ltac:(f_equal; rewrite NSV; clear; lia).
    setreg 24%Z (Z_to_bv 64 (Z.of_nat (length (skipn min la)))) ltac:(f_equal; rewrite LSK; clear - HMM; lia).
    eapply ua_loop; [exact I | | rewrite NSV, LSK; clear - HMM; lia | apply limbs_skipn; exact LLA | exact CV
                    | rewrite ELS; reflexivity | rewrite ELS; reflexivity].
    intros E0. rewrite E0 in LSK. cbn [length] in LSK. clear - LSK KD HMM. lia.
  Qed.

End Core.
