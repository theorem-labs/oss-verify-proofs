(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnModel BnAddSpec BnMInv.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Layout Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnKaraMem.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require W_usub_core.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop BnRepDefs AsStruct BnCallsA W_uadd_coreA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Notation usub_list := W_usub_core.usub_list.

Section Core.
  Variables (ra0 sp gp tp s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (jb : list byte).
  Variables (m1 : word -> option byte) (lo R A B Dr Da Db : Z) (br : bignum bptr) (la lb : list Z).
  Notation SP := (bv_unsigned sp).
  Notation max := (length la).
  Notation min := (length lb).
  Notation mx := (Z.of_nat (length la)).
  Notation mn := (Z.of_nat (length lb)).
  Notation dmx := (Z.of_nat (bn_dmax br)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).

  Definition usub_preA : Prop :=
    limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max <= bn_dmax br)%nat /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * mx <= lo /\ 0 <= Db /\ Db + 8 * mn <= lo /\ lo <= SP - 128 /\ SP <= 140737488355328)%Z /\
    (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z /\
    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z /\
    (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z /\
    (R mod 8 = 0 /\ A mod 8 = 0 /\ B mod 8 = 0 /\ Dr mod 8 = 0 /\ Da mod 8 = 0 /\ Db mod 8 = 0)%Z /\
    ((R + 24 <= SHLO \/ SHHI <= R) /\ (Dr + 8 * dmx <= SHLO \/ SHHI <= Dr) /\ SHHI <= lo)%Z.
  Hypothesis PRE : usub_preA.

  (* [comment removed for export] *)
  Lemma P_plain : W_usub_core.usub_pre sp lo R A B Dr Da Db br la lb.
  Proof.
    destruct PRE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & _).
    unfold W_usub_core.usub_pre. repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); assumption].
    change (2^64)%Z with 18446744073709551616%Z. lia.
  Qed.

  Lemma P_lists : limbs la /\ limbs lb /\ (min <= max)%nat /\ bn_okm br /\ (max <= bn_dmax br)%nat.
  Proof. destruct PRE as (H1 & H2 & H3 & H4 & H5 & _). auto. Qed.
  Lemma P_rng : (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * mx <= lo /\ 0 <= Db /\ Db + 8 * mn <= lo /\ lo <= SP - 128 /\ SP <= 140737488355328)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_lo : (lo <= SP - 128 /\ SP < 18446744073709551616)%Z.
  Proof. pose proof P_rng as H. lia. Qed.
  Lemma P_structs : (A = R \/ A + 8 <= R \/ R + 24 <= A)%Z /\ (B = R \/ B + 8 <= R \/ R + 24 <= B)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & H1 & H2 & _). auto. Qed.
  Lemma P_sarr : (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * mx <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * mn <= R)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _). auto. Qed.
  Lemma P_alias : (Da = Dr \/ Dr + 8 * dmx <= Da \/ Da + 8 * mx <= Dr)%Z /\ (Db = Dr \/ Dr + 8 * dmx <= Db \/ Db + 8 * mn <= Dr)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). auto. Qed.
  Lemma P_al : (R mod 8 = 0 /\ A mod 8 = 0 /\ B mod 8 = 0 /\ Dr mod 8 = 0 /\ Da mod 8 = 0 /\ Db mod 8 = 0)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_sh : ((R + 24 <= SHLO \/ SHHI <= R) /\ (Dr + 8 * dmx <= SHLO \/ SHHI <= Dr) /\ SHHI <= lo)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  Notation Wfin := [(Dr, Dr + 8 * mx); (R, R + 24); (SP - 128, SP)]%Z.
  Notation FRAME := [CB 8 jb; C8 s7_; C8 s6_; C8 s5_; C8 s4_; C8 s3_; C8 s2_; C8 s1_; C8 s0_; C8 ra0].

  Lemma P_off : offshW Wfin.
  Proof.
    pose proof P_sh as (H1 & H2 & H3). pose proof P_rng as RNG. pose proof P_lists as (_ & _ & _ & _ & HD).
    cbn [offshW]. unfold SHLO, SHHI in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Notation usub_buf := (W_usub_core.usub_buf br la lb).
  Notation usub_top := (W_usub_core.usub_top br la lb).
  Notation usub_bn := (W_usub_core.usub_bn br la lb).

  Lemma usub_buf_len : length usub_buf = bn_dmax br.
  Proof. exact (W_usub_core.usub_buf_len sp lo R A B Dr Da Db br la lb P_plain). Qed.
  Lemma usub_buf_limbs : limbs usub_buf.
  Proof. exact (W_usub_core.usub_buf_limbs sp lo R A B Dr Da Db br la lb P_plain). Qed.

  Definition usub_postA : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m2,
      ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0_ s1_ (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2_ s3_ s4_ s5_ s6_ s7_ s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra0) fc None m2 (seg_rom asegs)
      /\ munch Wfin m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2
      /\ rw_cells asegs m2 R (bn_cells Dr usub_bn) /\ u64arr asegs m2 Dr (wlimbs usub_buf)
      /\ stk asegs m2 lo SP.

  Notation ST pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma us_epi : forall m2 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6,
    rw_cells asegs m2 (SP + -80) FRAME -> stk asegs m2 lo (SP + -80) -> mem_inv asegs m2 ->
    munch Wfin m1 m2 -> wmono asegs m1 m2 ->
    rw_cells asegs m2 R (bn_cells Dr usub_bn) -> u64arr asegs m2 Dr (wlimbs usub_buf) ->
    evt asegs usub_postA (ST 0x25044c m2 x1 t0 t1 t2 x8 x9 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6).
  Proof.
    intros m2 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 FR ST MI MU WM SR UR.
    unfold bn_cells in SR.
    do 9 zstep.
    pose proof P_lo as PLO.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold usub_postA. do 14 eexists. exists m2. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [unfold bn_cells; exact SR|]. split; [exact UR | exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition core_memA : Prop :=
    rw_cells asegs m1 R (bn_cells Dr br) /\ u64arr asegs m1 Dr (wlimbs (bn_buf br)) /\
    rw_cells asegs m1 A [C8 (wz Da)] /\ rw_cells asegs m1 B [C8 (wz Db)] /\
    limbs_at asegs m1 Da la /\ limbs_at asegs m1 Db lb /\
    rw_cells asegs m1 (SP + -80) FRAME /\ stk asegs m1 lo (SP + -80) /\ mem_inv asegs m1 /\
    shb_cells asegs 5932248 6753336 m1 /\
    acc asegs m1 R 24 /\ acc asegs m1 A 8 /\ acc asegs m1 B 8 /\
    acc asegs m1 Dr (8 * dmx) /\ acc asegs m1 Da (8 * mx) /\ acc asegs m1 Db (8 * mn).
  Hypothesis MEM : core_memA.

  Lemma M_acc : acc asegs m1 R 24 /\ acc asegs m1 A 8 /\ acc asegs m1 B 8 /\
    acc asegs m1 Dr (8 * dmx) /\ acc asegs m1 Da (8 * mx) /\ acc asegs m1 Db (8 * mn).
  Proof. destruct MEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  Ltac shrd ACC MU p n k AL BD :=
    let ad := cur_mem_addr in let RD := fresh "RDsh" in
    pose proof (acc_rd_limb asegs _ m1 _ p n 0 k ad ACC MU P_off AL BD eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(sh_addr_k)) as RD;
    zstep; clear RD.

  (* [comment removed for export] *)
  Lemma us_top : forall m2 topv negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x23 t3 t4 t5 t6,
    rw_cells asegs m2 R [C8 (wz Dr); C4 topv; C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] ->
    u64arr asegs m2 Dr (wlimbs usub_buf) ->
    rw_cells asegs m2 (SP + -80) FRAME -> stk asegs m2 lo (SP + -80) -> mem_inv asegs m2 ->
    munch Wfin m1 m2 -> wmono asegs m1 m2 ->
    evt asegs usub_postA (ST 0x250418 m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat usub_top)) x19 x20 x21
                             (Z_to_bv 64 SHB) x23 t3 t4 t5 t6).
  Proof.
    intros m2 topv negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x23 t3 t4 t5 t6 SR UR FR ST MI MU WM.
    pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). pose proof P_al as (ALR & _). pose proof M_acc as (ACR & _).
    pose proof usub_buf_len as LU.
    assert (LW : length (wlimbs usub_buf) = bn_dmax br) by (rewrite wlimbs_len; exact LU).
    assert (BR : (0 <= R /\ R + 8 * 3 <= 140737488355328)%Z) by (clear - RNG; lia).
    do 3 zstep. shrd ACR MU R 3%Z 1%Z ALR BR. chk0.
    step.
    do 3 zstep. shrd ACR MU R 3%Z 2%Z ALR BR. chk0.
    step. zstep.
    eapply us_epi; try eassumption.
    unfold bn_cells, W_usub_core.usub_bn, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite LU. exact SR.
  Qed.

  (* [comment removed for export] *)
  Lemma us_strip : forall (t : nat) m2 topv negv x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 x19 x20 x21 x23 t3 t4 t5 t6,
    rw_cells asegs m2 R [C8 (wz Dr); C4 topv; C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] ->
    u64arr asegs m2 Dr (wlimbs usub_buf) ->
    rw_cells asegs m2 (SP + -80) FRAME -> stk asegs m2 lo (SP + -80) -> mem_inv asegs m2 ->
    munch Wfin m1 m2 -> wmono asegs m1 m2 ->
    (1 <= t <= max)%nat -> usub_top = strip_top usub_buf t ->
    evt asegs usub_postA (ST 0x2503f0 m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 (Dr + 8 * Z.of_nat t + -8)) a1 a2 a3 a4 a5 a6
                             (Z_to_bv 64 (Dr + 8 * Z.of_nat t + -8))
                             (Z_to_bv 64 (Z.of_nat t)) x19 x20 x21 (Z_to_bv 64 SHB) x23 t3 t4 t5 t6).
  Proof.
    induction t as [|t IH]; intros m2 topv negv x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 x19 x20 x21 x23 t3 t4 t5 t6 SR UR FR ST MI MU WM Ht ET;
      [exfalso; clear - Ht; lia|].
    pose proof P_lists as (_ & _ & _ & OKR & HD). pose proof OKR as (LBR & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    pose proof P_rng as RNG. pose proof P_al as (_ & _ & _ & ALDR & _). pose proof M_acc as (_ & _ & _ & ACDR & _).
    assert (BDR : (0 <= Dr /\ Dr + 8 * dmx <= 140737488355328)%Z) by (clear - RNG; lia).
    pose proof usub_buf_len as LU.
    pose proof (limbs_at_of_u64arr asegs m2 Dr usub_buf UR) as HL.
    destruct (nth_error usub_buf t) as [x|] eqn:Ex; [|apply nth_error_None in Ex; exfalso; clear - Ex LU Ht HD; lia].
    assert (Enth : nth t usub_buf 0%Z = x) by (apply nth_error_nth; exact Ex).
    cbn [strip_top] in ET. rewrite Enth in ET.
    pose proof (limbs_nth_error_lit usub_buf t x usub_buf_limbs Ex) as RX.
    do 2 zstep.
    shrd ACDR MU Dr (Z.of_nat (bn_dmax br)) (Z.of_nat t) ALDR BDR. chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth asegs m2 Dr usub_buf t x ad HL Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (x =? 0)%Z with false in ET by (symmetry; apply Z.eqb_neq; exact K).
      rewrite <- ET. eapply us_top; eassumption.
    - replace (x =? 0)%Z with true in ET by (symmetry; apply Z.eqb_eq; exact K).
      zstep. rewrite (bn_swrap32_small (Z.of_nat (S t) + -1)) by (clear - Ht HD DMR; lia).
      do 2 zstep. zstep. if_cases K2; zify_cond K2.
      + setreg 10%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat t + -8)) ltac:(f_equal; clear; lia).
        setreg 18%Z (Z_to_bv 64 (Z.of_nat t)) ltac:(f_equal; clear; lia).
        eapply IH; try eassumption. clear - Ht K2. lia.
      + assert (E0 : t = 0%nat) by (clear - K2; lia). subst t. cbn [strip_top] in ET.
        setreg 18%Z (Z_to_bv 64 (Z.of_nat usub_top)) ltac:(rewrite ET; reflexivity).
        eapply us_top; eassumption.
  Qed.

  Definition UB (m2 : word -> option byte) (pre l : list Z) (topv negv : word) : Prop :=
    rw_cells asegs m2 R [C8 (wz Dr); C4 topv; C4 (wz dmx); C4 negv; C4 (wz (bn_flags br))] /\
    limbs_at asegs m2 Dr pre /\ wr_at asegs m2 Dr (8 * dmx) /\
    limbs_at asegs m2 (Da + 8 * Z.of_nat (length pre)) l /\
    rw_cells asegs m2 (SP + -80) FRAME /\ stk asegs m2 lo (SP + -80) /\ mem_inv asegs m2 /\
    munch Wfin m1 m2 /\ wmono asegs m1 m2.

  Lemma UB_store : forall m2 pre x l topv negv v,
    UB m2 pre (x :: l) topv negv -> (length pre + S (length l) <= max)%nat ->
    store_ok asegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true /\
    UB (write_to_mem m2 (wa (Dr + 8 * Z.of_nat (length pre))) (le8 (Z_to_bv 64 v))) (pre ++ [v]) l topv negv.
  Proof.
    intros m2 pre x l topv negv v (SR & HP & HW & HL & FR & ST & MI & MU & WM) Hlen.
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _). pose proof P_alias as (AL & _).
    pose proof (limbs_at_bound _ _ _ _ HL) as BL. cbn [length] in BL.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    change (2^64)%Z with 18446744073709551616%Z in *.
    assert (SOK : store_ok asegs m2 (wa (Dr + 8 * Z.of_nat (length pre))) 8 = true).
    { apply (wr_at_store_ok asegs m2 Dr (8 * dmx)); [exact HW | lia | lia]. }
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

  Lemma us_final_arr : forall m2 w, munch Wfin m1 m2 -> wmono asegs m1 m2 -> limbs_at asegs m2 Dr w -> length w = max ->
    u64arr asegs m2 Dr (wlimbs (splice (bn_buf br) 0 w)).
  Proof.
    intros m2 w MU WM HWL Hlen.
    destruct MEM as (_ & UR1 & _).
    pose proof P_lists as (_ & _ & _ & _ & HD). pose proof P_rng as RNG. pose proof P_sarr as (SA1 & _).
    unfold bn_dmax in *.
    apply (limbarr_limbs_at asegs) in UR1. destruct UR1 as [HL1 HW1].
    assert (LS : length (splice (bn_buf br) 0 w) = length (bn_buf br)) by (apply splice_length; lia).
    apply u64arr_of_limbs_at.
    - replace Dr with (Dr + 8 * Z.of_nat 0)%Z in HWL by lia.
      replace Dr with (Dr + 8 * Z.of_nat 0)%Z at 1 by lia. rewrite Z.add_0_r.
      eapply (limbs_at_splice asegs Wfin m1 m2 Dr (bn_buf br) 0 w HL1 MU); [lia | exact HWL | |].
      + cbn [disjoint_from]. lia.
      + cbn [disjoint_from]. lia.
    - rewrite LS. eapply wr_at_transport; [exact HW1 | exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma us_strip_entry : forall m2 topv negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 x19 x20 x21 x23 t3 t4 t5 t6,
    (0 < max)%nat -> UB m2 (usub_list la lb) [] topv negv ->
    evt asegs usub_postA (ST 0x2503e8 m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Dr + 8 * mx))
                             (Z_to_bv 64 mx) x19 x20 x21 (Z_to_bv 64 SHB) x23 t3 t4 t5 t6).
  Proof.
    intros m2 topv negv x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 x19 x20 x21 x23 t3 t4 t5 t6 Hmax (SR & HP & _ & _ & FR & ST & MI & MU & WM).
    pose proof P_lists as (LLA & LLB & HMM & _ & _).
    pose proof (W_usub_core.usub_list_facts la lb LLA LLB HMM) as (_ & NW).
    assert (EBUF : usub_buf = splice (bn_buf br) 0 (usub_list la lb)).
    { unfold W_usub_core.usub_buf. destruct (Nat.eqb_spec max 0) as [E0|_]; [exfalso; clear - E0 Hmax; lia | reflexivity]. }
    do 2 zstep.
    eapply (us_strip max); [exact SR | rewrite EBUF; apply us_final_arr; assumption | exact FR | exact ST | exact MI | exact MU | exact WM
                           | clear - Hmax; lia | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma us_loop : forall l pre c m2 topv negv x1 t0 t1 t2 x8 a1 a7 x19 x20 x21 x23 t3 t4 t5 t6,
    UB m2 pre l topv negv -> l <> [] -> (length pre + length l = max)%nat -> limbs l -> (0 <= c <= 1)%Z ->
    usub_list la lb = pre ++ fst (sub_part_pos l c) ->
    evt asegs usub_postA
      (ST 0x250368 m2 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 c) a1 (Z_to_bv 64 (Dr + 8 * Z.of_nat (length pre)))
          (Z_to_bv 64 (shad (Da + 8 * Z.of_nat (length pre)))) (Z_to_bv 64 (shad (Dr + 8 * Z.of_nat (length pre))))
          (Z_to_bv 64 (- Z.of_nat (length l))) (Z_to_bv 64 (Da + 8 * Z.of_nat (length pre))) a7
          (Z_to_bv 64 mx) x19 x20 x21 (Z_to_bv 64 SHB) x23 t3 t4 t5 t6).
  Proof.
    induction l as [|x l IH]; intros pre c m2 topv negv x1 t0 t1 t2 x8 a1 a7 x19 x20 x21 x23 t3 t4 t5 t6 I NE HLEN LL HC E1;
      [exfalso; apply NE; reflexivity|]. clear NE.
    pose proof P_lists as (_ & _ & _ & OKR & HD). pose proof OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    pose proof P_rng as RNG. pose proof P_al as (_ & _ & _ & ALDR & ALDA & _).
    pose proof M_acc as (_ & _ & _ & ACDR & ACDA & _).
    assert (BDR : (0 <= Dr /\ Dr + 8 * dmx <= 140737488355328)%Z) by (clear - RNG; lia).
    assert (BDA : (0 <= Da /\ Da + 8 * mx <= 140737488355328)%Z) by (clear - RNG; lia).
    apply limbs_cons_lit in LL. destruct LL as [RX LL].
    pose proof I as (_ & _ & _ & HL & _ & _ & _ & MU0 & _).
    cbn [length] in HLEN.
    shrd ACDA MU0 Da (Z.of_nat (length la)) (Z.of_nat (length pre)) ALDA BDA. chk0.
    shrd ACDR MU0 Dr (Z.of_nat (bn_dmax br)) (Z.of_nat (length pre)) ALDR BDR. chk0.
    clear MU0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_hd asegs m2 _ x l ad HL ltac:(unfold wa; reflexivity)) as RD); zstep; clear RD.
    do 5 zstep.
    zstep. zstep.
    setreg 6%Z (Z_to_bv 64 ((x - c) mod BW)) ltac:(apply Z_to_bv_eqm; rewrite BW_lit; clear; Z.div_mod_to_equations; lia).
    destruct (UB_store m2 pre x l _ negv ((x - c) mod BW)%Z I ltac:(clear - HLEN; lia)) as [SOK I2].
    zstep. store_bundleA I2.
    zstep.
    setreg 10%Z (Z_to_bv 64 (if x =? 0 then c else 0)%Z)
      ltac:(f_equal; clear - HC RX; destruct (Z.eqb_spec x 0) as [E0|N0];
            [rewrite E0; cbn [Z.ltb Z.compare Z.b2z]; assert (c = 0 \/ c = 1)%Z as [->| ->] by lia; reflexivity
            |replace (x <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity]).
    do 2 zstep.
    setreg 15%Z (Z_to_bv 64 (- Z.of_nat (length l)))
      ltac:(f_equal; cbn [length]; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia;
            change (2^64)%Z with 18446744073709551616%Z; rewrite bn_swrap32_mod by (clear - HLEN HD DMR; lia); clear; lia).
    assert (E1' : usub_list la lb = (pre ++ [((x - c) mod BW)%Z]) ++ fst (sub_part_pos l (if x =? 0 then c else 0)%Z)).
    { rewrite E1, W_usub_core.sub_part_pos_cons. cbn [fst]. rewrite <- app_assoc. reflexivity. }
    assert (HC' : (0 <= (if x =? 0 then c else 0) <= 1)%Z) by (clear - HC; destruct (x =? 0)%Z; lia).
    assert (LP : length (pre ++ [((x - c) mod BW)%Z]) = (length pre + 1)%nat) by (rewrite length_app; reflexivity).
    setreg 12%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (length (pre ++ [((x - c) mod BW)%Z])))) ltac:(f_equal; rewrite LP; clear; lia).
    setreg 16%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (length (pre ++ [((x - c) mod BW)%Z])))) ltac:(f_equal; rewrite LP; clear; lia).
    setreg 13%Z (Z_to_bv 64 (shad (Da + 8 * Z.of_nat (length (pre ++ [((x - c) mod BW)%Z])))))
      ltac:(f_equal; rewrite LP, shad_next by (clear - ALDA; Z.div_mod_to_equations; lia); f_equal; clear; lia).
    setreg 14%Z (Z_to_bv 64 (shad (Dr + 8 * Z.of_nat (length (pre ++ [((x - c) mod BW)%Z])))))
      ltac:(f_equal; rewrite LP, shad_next by (clear - ALDR; Z.div_mod_to_equations; lia); f_equal; clear; lia).
    zstep. if_cases KZ; zify_cond KZ.
    - assert (NE : l <> []) by (intros ->; apply KZ; reflexivity).
      eapply IH; [exact I2 | exact NE | rewrite LP; clear - HLEN; lia | exact LL | exact HC' | exact E1'].
    - rewrite land64_zero_iff in KZ by (clear - HLEN HD DMR; lia).
      assert (EL : l = []) by (clear - KZ; destruct l; [reflexivity | cbn [length] in KZ; lia]). subst l.
      cbn [sub_part_pos fst] in E1'. rewrite app_nil_r in E1'.
      zstep.
      setreg 17%Z (Z_to_bv 64 (Dr + 8 * mx)) ltac:(f_equal; rewrite LP; clear - HLEN; cbn [length] in HLEN; lia).
      rewrite <- E1' in I2.
      eapply us_strip_entry; [clear - HLEN; lia | exact I2].
  Qed.

  (* [comment removed for export] *)
  Lemma usub_coreA : forall x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt asegs usub_postA
      (ST 0x2502e8 m1 x1 t0 t1 t2 x8 (Z_to_bv 64 R) (Z_to_bv 64 R) a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 mx) (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 mn) (Z_to_bv 64 SHB) (Z_to_bv 64 (mx - mn)) t3 t4 t5 t6).
  Proof.
    intros x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & FR & ST & MI & (SHB1 & SHB2) & ACR & ACA & ACB & ACDR & ACDA & ACDB).
    pose proof P_lists as (LLA & LLB & HMM & OKR & HD).
    pose proof P_rng as RNG. pose proof P_al as (ALR & ALA & ALB & ALDR & ALDA & ALDB). pose proof P_sh as (SHR & SHDR & SHLOlo).
    pose proof OKR as (_ & _ & DMR & _). unfold BN_WORDS_MAX in DMR.
    pose proof (munch_refl Wfin m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    assert (BR : (0 <= R /\ R + 8 * 3 <= 140737488355328)%Z) by (clear - RNG; lia).
    assert (BA : (0 <= A /\ A + 8 * 1 <= 140737488355328)%Z) by (clear - RNG; lia).
    assert (BB : (0 <= B /\ B + 8 * 1 <= 140737488355328)%Z) by (clear - RNG; lia).
    unfold bn_cells in SR.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K RNG; lia|]. clear K.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (E0 : max = 0%nat) by (clear - K0; lia).
      assert (ETOP : usub_top = 0%nat) by (unfold W_usub_core.usub_top; rewrite E0; reflexivity).
      assert (EBUF : usub_buf = bn_buf br) by (unfold W_usub_core.usub_buf; rewrite E0; reflexivity).
      replace (Z_to_bv 64 mx) with (Z_to_bv 64 (Z.of_nat usub_top)) by (rewrite ETOP, E0; reflexivity).
      eapply (us_top m1); [exact SR | rewrite EBUF; exact UR | exact FR | exact ST | exact MI | exact MU | exact WM]. }
    assert (Hmax : (0 < max)%nat) by (clear - K0; lia). clear K0.
    do 2 zstep. shrd ACA MU A 1%Z 0%Z ALA BA. chk0.
    do 2 zstep. shrd ACB MU B 1%Z 0%Z ALB BB. chk0.
    do 2 zstep. shrd ACR MU R 3%Z 0%Z ALR BR. chk0.
    do 6 zstep.
    (* [comment removed for export] *)
    pose proof P_alias as (ALIA & ALIB). pose proof P_sarr as (SA1 & SA2 & SA3).
    assert (HW : wr_at asegs m1 Dr (8 * dmx)).
    { apply (limbarr_limbs_at asegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    assert (LF : length (firstn min la) = min) by (apply firstn_length_le; exact HMM).
    assert (ESPF : bv_unsigned SPF = (SP + -80)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    eapply (call_sub_wordsA usub_postA) with (a := firstn min la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -80)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | split; [exact SHB1 | exact SHB2]
      | apply limbs_firstn; exact LLA | exact LLB | rewrite LF; reflexivity | rewrite LF; clear - HMM HD DMR; lia
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | rewrite LF; apply unsigned_lit; clear - HMM HD DMR; lia
      | apply (limbs_at_firstn asegs); exact HLA | exact HLB
      | rewrite LF; replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HMM HD; lia]
      | rewrite LF; unfold alias_ok; clear - ALIA HMM HD; lia | rewrite LF; unfold alias_ok; clear - ALIB HMM HD; lia
      | clear - RNG; lia | rewrite LF; clear - RNG HMM HD; lia | rewrite LF; clear - RNG HMM; lia | rewrite LF; clear - RNG; lia
      | rewrite LF; eapply acc_sub; [exact ACDR | lia | clear - HMM HD; lia]
      | rewrite LF; eapply acc_sub; [exact ACDA | lia | clear - HMM; lia]
      | rewrite LF; exact ACDB
      | rewrite LF; unfold aptrs3; clear - ALDR ALDA ALDB SHDR SHLOlo HMM HD; lia | ].
    rewrite LF. intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.
    pose proof (sub_words_spec (firstn min la) lb (limbs_firstn _ _ LLA) LLB LF) as AWS.
    assert (ELS : usub_list la lb = fst (sub_words (firstn min la) lb) ++ fst (sub_part_pos (skipn min la) (snd (sub_words (firstn min la) lb)))).
    { unfold W_usub_core.usub_list. destruct (sub_words (firstn min la) lb) as [sv cv]. cbn [fst snd]. destruct (sub_part_pos (skipn min la) cv). reflexivity. }
    destruct (sub_words (firstn min la) lb) as [sv cv]. cbn [fst snd] in *. destruct AWS as (LSV & NSV & CV & _). rewrite LF in NSV.
    assert (HL2 : limbs_at asegs m2 (Da + 8 * Z.of_nat (length sv)) (skipn min la)).
    { rewrite NSV. eapply limbs_at_transport; [apply (limbs_at_skipn asegs); [exact HLA | exact HMM] | exact MUc |].
      cbn [disjoint_from]. rewrite length_skipn. clear - ALIA RNG HMM HD. lia. }
    assert (I : UB m2 sv (skipn min la) (wz (Z.of_nat (bn_top br))) (wz (Z.b2z (bn_neg br)))).
    { unfold UB. split.
      { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 RNG HMM HD; lia]. }
      split; [exact HRc|]. split; [eapply wr_at_transport; [exact HW | exact WMc]|]. split; [exact HL2|].
      split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn; clear - RNG HMM HD; lia]. }
      split; [exact STc|]. split; [exact MIc|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HMM. lia. }
      eapply wmono_trans; [exact WM | exact WMc]. }
    clear SR UR HAd HBd FR ST MI MU WM HLA HLB HW MUc WMc MIc HRc STc HL2 SHB1 SHB2.
    zstep. replace (Z.shiftl mn 3) with (8 * mn)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    assert (LSK : length (skipn min la) = (max - min)%nat) by apply length_skipn.
    zstep. if_cases KD; zify_cond KD.
    { (* [comment removed for export] *)
      assert (ESK : skipn min la = []) by (clear - KD LSK; destruct (skipn min la); [reflexivity | cbn [length] in LSK; lia]).
      rewrite ESK in ELS, I. cbn [sub_part_pos fst] in ELS. rewrite app_nil_r in ELS.
      zstep.
      setreg 17%Z (Z_to_bv 64 (Dr + 8 * mx)) ltac:(f_equal; clear - KD; lia).
      eapply us_strip_entry; [exact Hmax | rewrite ELS; exact I]. }
    do 8 zstep.
    rewrite (bn_swrap32_small (mn - mx)) by (clear - HMM HD DMR; lia).
    setreg 15%Z (Z_to_bv 64 (- Z.of_nat (length (skipn min la)))) ltac:(f_equal; rewrite LSK; clear - HMM; lia).
    setreg 13%Z (Z_to_bv 64 (shad (Da + 8 * Z.of_nat (length sv))))
      ltac:(f_equal; unfold shad; rewrite NSV, Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 14%Z (Z_to_bv 64 (shad (Dr + 8 * Z.of_nat (length sv))))
      ltac:(f_equal; unfold shad; rewrite NSV, Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; clear; lia).
    setreg 12%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat (length sv))) ltac:(f_equal; rewrite NSV; clear; lia).
    setreg 16%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (length sv))) ltac:(f_equal; rewrite NSV; clear; lia).
    eapply us_loop; [exact I | | rewrite NSV, LSK; clear - HMM; lia | apply limbs_skipn; exact LLA | exact CV | rewrite ELS; reflexivity].
    intros E0. rewrite E0 in LSK. cbn [length] in LSK. clear - LSK KD HMM. lia.
  Qed.
End Core.
