(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_cmp_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Notation bgusegs := ImageBg.bgusegs.
Definition BN_UCMP_U : Z := 0xfecac.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo A B Da Db : Z) (ba bb : bignum bptr).
  Notation SP := (bv_unsigned sp).
  Notation la := (firstn (bn_top ba) (bn_buf ba)).
  Notation lb := (firstn (bn_top bb) (bn_buf bb)).
  Hypothesis SA : rw_cells bgusegs m A (bn_cells Da ba).
  Hypothesis SB : rw_cells bgusegs m B (bn_cells Db bb).
  Hypothesis RA : limbs_at bgusegs m Da la.
  Hypothesis RB : limbs_at bgusegs m Db lb.
  Hypothesis OKA : bn_okm ba.
  Hypothesis OKB : bn_okm bb.
  Hypothesis A0 : (0 < A)%Z.
  Hypothesis B0 : (0 < B)%Z.
  Hypothesis UA : hide (A mod 8 = 0)%Z.
  Hypothesis UB : hide (B mod 8 = 0)%Z.
  Hypothesis UDA : ub_ptr_ok (Z.of_nat (bn_top ba)) Da.
  Hypothesis UDB : ub_ptr_ok (Z.of_nat (bn_top bb)) Db.
  Hypothesis STK : stk bgusegs m lo SP.
  Hypothesis LO : (lo <= SP - 80)%Z.
  Hypothesis SEPA : (A + 24 <= SP - 80 \/ SP <= A)%Z.
  Hypothesis SEPB : (B + 24 <= SP - 80 \/ SP <= B)%Z.
  Hypothesis SEPDA : (Da + 8 * Z.of_nat (bn_top ba) <= SP - 80 \/ SP <= Da)%Z.
  Hypothesis SEPDB : (Db + 8 * Z.of_nat (bn_top bb) <= SP - 80 \/ SP <= Db)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  Hypothesis EA0 : a0 = Z_to_bv 64 A.
  Hypothesis EA1 : a1 = Z_to_bv 64 B.

  Notation POST := (ro_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80%Z (ucmp_pure ba bb) lo m).

  (* [comment removed for export] *)
  Notation ST pc mm x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  (* [comment removed for export] *)
  Definition UINV (m1 : word -> option byte) : Prop :=
    limbs_at bgusegs m1 Da la /\ limbs_at bgusegs m1 Db lb /\
    (exists jb, rw_cells bgusegs m1 (SP + -80) [CB 16 jb; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    stk bgusegs m1 lo (SP + -80) /\
    mem_inv bgusegs m1 /\ munch [(SP + -80, SP)]%Z m m1 /\ wmono bgusegs m m1 /\ (lo <= SP + -80)%Z.

  Ltac clr := clear SEPA SEPB SEPDA SEPDB LO STK MI0 RA RB SA SB UDA UDB UA UB A0 B0 EA0 EA1.

  (* [comment removed for export] *)
  Lemma uc_ret : forall m1 res x8 x10 x12 x13 x14 x15 x16 x17, UINV m1 -> res = ucmp_pure ba bb ->
    (-2147483648 <= res < 2147483648)%Z ->
    evt bgusegs POST (ST 0xfef90 m1 x8 x10 (Z_to_bv 64 res) x12 x13 x14 x15 x16 x17).
  Proof.
    clr. intros m1 res x8 x10 x12 x13 x14 x15 x16 x17 (HA & HB & (jb & FR) & ST & MI & MU & WM & LO') -> RR.
    zstep.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by (clear; lia).
    change (2 ^ 64)%Z with 18446744073709551616%Z. rewrite (bn_swrap32_mod (ucmp_pure ba bb) 0) by (clear - RR; lia). rewrite Z.add_0_r.
    do 8 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma uc_zero : forall m1 x8 x10 x11 x12 x13 x14 x15 x16 x17, UINV m1 -> ucmp_pure ba bb = 0%Z ->
    evt bgusegs POST (ST 0xfed94 m1 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    clr. intros m1 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    do 2 zstep.
    eapply uc_ret; [exact I | symmetry; exact E | clear; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma uc_differ : forall m1 x y x8 x10 x11 x12 x13 x14 x17, UINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = ucmp_pure ba bb ->
    evt bgusegs POST (ST 0xfefbc m1 x8 x10 x11 x12 x13 x14 (Z_to_bv 64 x) (Z_to_bv 64 y) x17).
  Proof.
    clr. intros m1 x y x8 x10 x11 x12 x13 x14 x17 I Rx Ry NE E.
    do 3 zstep.
    setreg 11%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep.
    eapply uc_ret; [exact I | exact E |].
    unfold cmp1. destruct (x =? y)%Z; [clear; lia|]. destruct (y <? x)%Z; clear; lia.
  Qed.

  (* [comment removed for export] *)
  Definition PTRS : Prop :=
    (0 < Da /\ Da mod 8 = 0 /\ Da + 8 * Z.of_nat (bn_top ba) <= 140737488355328 /\
     0 < Db /\ Db mod 8 = 0 /\ Db + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z.

  (* [comment removed for export] *)
  Lemma uc_loop : forall (k : nat) m1 x8 x15 x16 x17, UINV m1 -> PTRS -> (S k <= bn_top ba)%nat -> bn_top bb = bn_top ba ->
    ucmp_pure ba bb = cmp_words (firstn (S k) la) (firstn (S k) lb) ->
    evt bgusegs POST (ST 0xfed3c m1 x8 (Z_to_bv 64 (Z.of_nat (S k))) (Z_to_bv 64 1) (Z_to_bv 64 Db) (Z_to_bv 64 Da) (Z_to_bv 64 1) x15 x16 x17).
  Proof.
    clr. induction k as [k IH] using lt_wf_ind; intros m1 x8 x15 x16 x17 I PT Hk ET E.
    pose proof I as (HA & HB & _).
    pose proof OKA as (LMA & TDA & DMA & _). pose proof OKB as (LMB & TDB & DMB & _).
    assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
    assert (LLB : length lb = bn_top ba) by (rewrite firstn_length_le; [exact ET | clear - TDB ET; unfold bn_dmax in *; lia]).
    destruct (nth_error la k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; exfalso; clear - Ex LLA Hk; lia].
    destruct (nth_error lb k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; exfalso; clear - Ey LLB Hk; lia].
    pose proof (limbs_nth_error_lit la k x (limbs_firstn _ _ LMA) Ex) as Rx.
    pose proof (limbs_nth_error_lit lb k y (limbs_firstn _ _ LMB) Ey) as Ry.
    assert (PA : (0 < Da /\ Da + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z) by (clear - PT; unfold PTRS in PT; tauto).
    assert (PB : (0 < Db /\ Db + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z) by (clear - PT; unfold PTRS in PT; tauto).
    assert (Hk' : (Z.of_nat k < Z.of_nat (bn_top ba))%Z) by (clear - Hk; lia).
    zstep.
    rewrite (bn_swrap32_small (Z.of_nat (S k) + -1)) by (clear - Hk TA31; lia).
    replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by (clear; lia).
    do 2 zstep.
    rewrite (Z.shiftl_mul_pow2 (Z.of_nat k) 3) by (clear; lia). change (2 ^ 3)%Z with 8%Z.
    chk ltac:(fun C => clear - C PA Hk'; lia).
    do 2 zstep.
    replace (Da + Z.of_nat k * 8 <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - PA; lia).
    change (Z.lxor 1 (Z.b2z false)) with 1%Z.
    chk_lit.
    chk ltac:(fun C => clear - C PA; lia).
    zstep.
    rewrite (land7 (Da + Z.of_nat k * 8)) by (clear - PT; unfold PTRS in PT; destruct PT as (_ & M & _); Z.div_mod_to_equations; lia).
    chk_lit.
    zstep.
    chk ltac:(fun C => clear - C PB Hk'; lia).
    do 2 zstep.
    replace (Db + Z.of_nat k * 8 <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - PB; lia).
    change (Z.lxor 1 (Z.b2z false)) with 1%Z.
    chk_lit.
    chk ltac:(fun C => clear - C PB; lia).
    zstep.
    rewrite (land7 (Db + Z.of_nat k * 8)) by (clear - PT; unfold PTRS in PT; destruct PT as (_ & _ & _ & _ & M & _); Z.div_mod_to_equations; lia).
    chk_lit.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 Da la k x ad HA Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 Db lb k y ad HB Ey ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top la lb k x y ltac:(rewrite LLA, LLB; reflexivity) Ex Ey) as T.
    zstep. if_cases K2; zify_cond K2.
    { eapply uc_differ; [exact I | exact Rx | exact Ry | exact K2 |].
      rewrite E, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity]. }
    assert (E' : ucmp_pure ba bb = cmp_words (firstn k la) (firstn k lb)).
    { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
    zstep. rewrite lts_small by (clear - Hk TA31; lia). if_cases K4; zify_cond K4.
    - destruct k as [|k']; [exfalso; clear - K4; lia|].
      eapply (IH k'); [clear; lia | exact I | exact PT | clear - Hk; lia | exact ET | exact E'].
    - assert (K0 : k = 0%nat) by (clear - K4; lia). subst k.
      eapply uc_zero; [exact I|]. rewrite E'. reflexivity.
  Qed.

  Lemma BN_ucmp_uspec :
    evt bgusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BN_UCMP_U) fc None m (seg_rom bgusegs)).
  Proof.
    unfold BN_UCMP_U. subst a0 a1.
    pose proof (munch_refl [(SP - 80, SP)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold bn_cells in SA, SB.
    pose proof OKA as (LMA & TDA & DMA & FLA). pose proof OKB as (LMB & TDB & DMB & FLB).
    assert (FRA : (0 <= bn_flags ba <= 1)%Z) by (clear - FLA; destruct FLA as [E|E]; rewrite E; lia).
    assert (FRB : (0 <= bn_flags bb <= 1)%Z) by (clear - FLB; destruct FLB as [E|E]; rewrite E; lia).
    assert (EL4A : Z.land (bn_flags ba) 4 = 0%Z) by (clear - FLA; destruct FLA as [E|E]; rewrite E; reflexivity).
    assert (EL4B : Z.land (bn_flags bb) 4 = 0%Z) by (clear - FLB; destruct FLB as [E|E]; rewrite E; reflexivity).
    assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (TB31 : (0 <= Z.of_nat (bn_top bb) < 8388608)%Z) by (clear - TDB DMB; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
    assert (LLB : length lb = bn_top bb) by (rewrite firstn_length_le; [reflexivity | clear - TDB; unfold bn_dmax in *; lia]).
    unfold wz in SA, SB.
    apply (flag_cell_split bgusegs m A _ _ _ _ (bn_flags ba) FRA) in SA.
    apply (flag_cell_split bgusegs m B _ _ _ _ (bn_flags bb) FRB) in SB.
    pose proof (rw_cells_bound _ _ _ _ SA) as BA_. pose proof (rw_cells_bound _ _ _ _ SB) as BB_. cbn [cells_size csize Nat.add] in BA_, BB_.
    assert (PT0 : hide ((0 < Z.of_nat (bn_top ba))%Z -> bn_top bb = bn_top ba -> PTRS)).
    { apply hide_intro. intros HT ET. unfold PTRS.
      destruct (UDA HT) as (PA1 & PA2). destruct (UDB ltac:(rewrite ET; exact HT)) as (PB1 & PB2).
      assert (NEa : lbytes la <> []) by (destruct la; [cbn [length] in LLA; clear - LLA HT; lia | cbn; discriminate]).
      assert (NEb : lbytes lb <> []) by (destruct lb; [cbn [length] in LLB; rewrite ET in LLB; clear - LLB HT; lia | cbn; discriminate]).
      pose proof (bytes_at_below bgusegs m Da (lbytes la) MI0 RA NEa) as TA.
      pose proof (bytes_at_below bgusegs m Db (lbytes lb) MI0 RB NEb) as TB.
      rewrite lbytes_lengthZ in TA, TB. rewrite LLA in TA. rewrite LLB, ET in TB. unfold UTOP in TA, TB.
      repeat (split; [assumption|]). assumption. }
    carve_frame 80%nat STK.
    do 10 zstep.
    assert (I : UINV m1).
    { unfold UINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; rewrite LLA; clear - SEPDA; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LLB; clear - SEPDB; lia].
      - split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU|]. split; [exact WM | exact LO]. }
    clear RA RB FR STK MU WM.

    zstep. if_cases K; zify_cond K; [exfalso; clear - K A0; lia|]. clear K.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K B0; lia|]. clear K.
    zstep. rewrite (land7 A (hide_elim _ UA)). chk_lit.
    zstep. rewrite (land7 B (hide_elim _ UB)). chk_lit.
    zstep. cbv beta. rewrite (u8_lit (bn_flags ba)) by (clear - FRA; lia).
    do 3 zstep.
    rewrite EL4A. zstep. if_false.
    zstep. cbv beta. rewrite (u8_lit (bn_flags bb)) by (clear - FRB; lia).
    zstep. rewrite EL4B. zstep. if_false.
    zstep. rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - TA31; lia).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - TB31; lia).
    do 2 zstep.
    rewrite (bn_swrap32_small (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb))) by (clear - TA31 TB31; lia).
    replace (Z.of_nat (bn_top ba) + - Z.of_nat (bn_top bb))%Z with (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb))%Z by (clear; lia).
    chk ltac:(fun C => clear - C; lia).
    zstep.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by (clear; lia).
    change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite (bn_swrap32_mod (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb)) 0) by (clear - TA31 TB31; lia). rewrite Z.add_0_r.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      eapply uc_ret; [exact I | | clear - TA31 TB31; lia]. unfold ucmp_pure. cbv zeta.
      destruct (Z.eqb_spec (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb)) 0) as [E0|_]; [contradiction | reflexivity].
    - rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      assert (ET : bn_top bb = bn_top ba) by (clear - K; lia).
      zstep. rewrite (bn_swrap32_small (Z.of_nat (bn_top ba) + -1)) by (clear - TA31; lia).
      zstep. rewrite lts_signed by (clear - TA31; lia). if_cases C; [exfalso; zify_cond C; clear - C; lia | clear C].
      zstep. rewrite lts_signed by (clear - TA31; lia). if_cases K3; zify_cond K3.
      { (* [comment removed for export] *)
        eapply uc_zero; [exact I|]. unfold ucmp_pure. cbv zeta. rewrite K. cbn [Z.eqb].
        assert (T0 : bn_top ba = 0%nat) by (clear - K3; lia). rewrite ET, T0. reflexivity. }
      assert (PT : PTRS).
      { apply hide_elim in PT0. apply PT0; [clear - K3; lia | exact ET]. }
      do 2 zstep.
      replace (Z.land Da 18446744073709551615) with Da
        by (symmetry; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; clear - PT; unfold PTRS in PT; lia).
      replace (Z.land Db 18446744073709551615) with Db
        by (symmetry; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; clear - PT; unfold PTRS in PT; lia).
      replace (0 <? Da)%Z with true by (symmetry; apply Z.ltb_lt; clear - PT; unfold PTRS in PT; lia).
      replace (0 <? Db)%Z with true by (symmetry; apply Z.ltb_lt; clear - PT; unfold PTRS in PT; lia).
      change (Z.b2z true) with 1%Z.
      assert (EK : exists k, bn_top ba = S k) by (clear - K3; destruct (bn_top ba); [exfalso; lia | eexists; reflexivity]).
      destruct EK as (k & EK).
      setreg 10%Z (Z_to_bv 64 (Z.of_nat (S k))) ltac:(rewrite EK; reflexivity).
      eapply uc_loop; [exact I | exact PT | rewrite EK; clear; lia | exact ET |].
      unfold ucmp_pure. cbv zeta. rewrite K. cbn [Z.eqb].
      rewrite <- EK, ET, !firstn_firstn, Nat.min_id. reflexivity.
  Qed.
End Proofs.
