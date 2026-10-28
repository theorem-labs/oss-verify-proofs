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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Notation bgusegs := ImageBg.bgusegs.
Definition BN_CMP_U : Z := 0xfefe0.

(* [comment removed for export] *)
Lemma lor_land7 : forall a b, (a mod 8 = 0)%Z -> (b mod 8 = 0)%Z -> Z.land (Z.lor a b) 7 = 0%Z.
Proof. intros a b Ha Hb. rewrite Z.land_lor_distr_l, (land7 a Ha), (land7 b Hb). reflexivity. Qed.

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
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (A + 24 <= SP - 16 \/ SP <= A)%Z.
  Hypothesis SEPB : (B + 24 <= SP - 16 \/ SP <= B)%Z.
  Hypothesis SEPDA : (Da + 8 * Z.of_nat (bn_top ba) <= SP - 16 \/ SP <= Da)%Z.
  Hypothesis SEPDB : (Db + 8 * Z.of_nat (bn_top bb) <= SP - 16 \/ SP <= Db)%Z.
  Hypothesis MI0 : mem_inv bgusegs m.
  Hypothesis EA0 : a0 = Z_to_bv 64 A.
  Hypothesis EA1 : a1 = Z_to_bv 64 B.

  Notation POST := (ro_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_pure ba bb) lo m).

  Definition gtv : Z := if bn_neg ba then -1 else 1.
  Definition ltv : Z := if bn_neg ba then 1 else -1.

  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  (* [comment removed for export] *)
  Definition BINV (m1 : word -> option byte) : Prop :=
    limbs_at bgusegs m1 Da la /\ limbs_at bgusegs m1 Db lb /\
    rw_cells bgusegs m1 A (bn_cells Da ba) /\ rw_cells bgusegs m1 B (bn_cells Db bb) /\
    rw_cells bgusegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bgusegs m1 lo (SP + -16) /\
    mem_inv bgusegs m1 /\ munch [(SP + -16, SP)]%Z m m1 /\ wmono bgusegs m m1 /\ (lo <= SP + -16)%Z.

  (* [comment removed for export] *)
  Lemma bc_ret : forall m1 res x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17, BINV m1 -> res = cmp_pure ba bb ->
    evt bgusegs POST (ST 0xff054 m1 x5 x6 x7 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    clear SEPA SEPB SEPDA SEPDB LO STK MI0 RA RB SA SB UDA UDB UA UB A0 B0 EA0 EA1.
    intros m1 res x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 (HA & HB & _ & _ & FR & ST & MI & MU & WM & LO') ->.
    do 2 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma bc_zero : forall m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17, BINV m1 -> cmp_pure ba bb = 0%Z ->
    evt bgusegs POST (ST 0xff0dc m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    clear SEPA SEPB SEPDA SEPDB LO STK MI0 RA RB SA SB UDA UDB UA UB A0 B0 EA0 EA1.
    intros m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    do 2 zstep.
    eapply bc_ret; [exact I | symmetry; exact E].
  Qed.

  Lemma cmp_pure_tops_eq : Bool.eqb (bn_neg ba) (bn_neg bb) = true -> bn_top bb = bn_top ba ->
    cmp_pure ba bb = (if cmp_words la lb =? 0 then 0 else if 0 <? cmp_words la lb then gtv else ltv)%Z.
  Proof.
    intros EN ET. unfold cmp_pure, gtv, ltv. rewrite EN. cbn [negb]. cbv zeta. rewrite ET, Nat.ltb_irrefl. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition PTRS : Prop :=
    (0 < Da /\ Da mod 8 = 0 /\ Da + 8 * Z.of_nat (bn_top ba) <= 140737488355328 /\
     0 < Db /\ Db mod 8 = 0 /\ Db + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z.

  (* [comment removed for export] *)
  Lemma bc_loop : forall (k : nat) m1 x5 x6 x7 x8 x16 x17, BINV m1 -> PTRS -> (S k <= bn_top ba)%nat ->
    Bool.eqb (bn_neg ba) (bn_neg bb) = true -> bn_top bb = bn_top ba ->
    cmp_words la lb = cmp_words (firstn (S k) la) (firstn (S k) lb) ->
    evt bgusegs POST (ST 0xff078 m1 x5 x6 x7 x8 (Z_to_bv 64 gtv) (Z_to_bv 64 B) (Z_to_bv 64 Da) (Z_to_bv 64 (Z.of_nat (S k)))
                       (Z_to_bv 64 ltv) (Z_to_bv 64 1) x16 x17).
  Proof.
    clear SEPA SEPB SEPDA SEPDB LO STK MI0 RA RB SA SB UDA UDB UA UB A0 B0 EA0 EA1.
    induction k as [k IH] using lt_wf_ind; intros m1 x5 x6 x7 x8 x16 x17 I PT Hk EN ET E.
    pose proof I as (HA & HB & SA1 & SB1 & _).
    unfold bn_cells, wz in SA1, SB1.
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
    zstep. zstep.
    chk ltac:(fun C => clear - C PB Hk'; lia).
    do 3 zstep.
    replace (Db + Z.of_nat k * 8 <? 1)%Z with false by (symmetry; apply Z.ltb_ge; clear - PB; lia).
    replace (0 <? Db)%Z with true by (symmetry; apply Z.ltb_lt; clear - PB; lia).
    change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1%Z.
    chk_lit.
    chk ltac:(fun C => clear - C PB; lia).
    zstep.
    rewrite (land7 (Db + Z.of_nat k * 8)) by (clear - PT; unfold PTRS in PT; destruct PT as (_ & _ & _ & _ & M & _); Z.div_mod_to_equations; lia).
    chk_lit.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 Da la k x ad HA Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgusegs m1 Db lb k y ad HB Ey ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top la lb k x y ltac:(rewrite LLA, LLB; reflexivity) Ex Ey) as T.
    zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      eapply bc_ret; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E, T. unfold cmp1.
      destruct (Z.eqb_spec x y) as [E0|_]; [exfalso; clear - E0 K2; lia|].
      replace (y <? x)%Z with true by (symmetry; apply Z.ltb_lt; exact K2). reflexivity. }
    zstep. if_cases K3; zify_cond K3.
    { (* [comment removed for export] *)
      do 2 zstep.
      eapply bc_ret; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E, T. unfold cmp1.
      destruct (Z.eqb_spec x y) as [E0|_]; [exfalso; clear - E0 K3; lia|].
      replace (y <? x)%Z with false by (symmetry; apply Z.ltb_ge; clear - K2; lia). reflexivity. }
    (* [comment removed for export] *)
    assert (Exy : x = y) by (clear - K2 K3; lia).
    assert (E' : cmp_words la lb = cmp_words (firstn k la) (firstn k lb)).
    { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
    zstep. rewrite lts_small by (clear - Hk TA31; lia). if_cases K4; zify_cond K4.
    - destruct k as [|k']; [exfalso; clear - K4; lia|].
      eapply (IH k'); [clear; lia | exact I | exact PT | clear - Hk; lia | exact EN | exact ET | exact E'].
    - assert (K0 : k = 0%nat) by (clear - K4; lia). subst k.
      eapply bc_zero; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E'. reflexivity.
  Qed.

  Lemma BN_cmp_uspec :
    evt bgusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BN_CMP_U) fc None m (seg_rom bgusegs)).
  Proof.
    unfold BN_CMP_U. subst a0 a1.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    pose proof SA as SA'. pose proof SB as SB'.
    unfold bn_cells in SA', SB'.
    pose proof OKA as (LMA & TDA & DMA & FLA). pose proof OKB as (LMB & TDB & DMB & FLB).
    assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (TB31 : (0 <= Z.of_nat (bn_top bb) < 8388608)%Z) by (clear - TDB DMB; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
    assert (LLB : length lb = bn_top bb) by (rewrite firstn_length_le; [reflexivity | clear - TDB; unfold bn_dmax in *; lia]).
    assert (NA : (0 <= Z.b2z (bn_neg ba) <= 1)%Z) by (destruct (bn_neg ba); cbn; lia).
    assert (NB : (0 <= Z.b2z (bn_neg bb) <= 1)%Z) by (destruct (bn_neg bb); cbn; lia).
    unfold wz in SA', SB'.
    pose proof (rw_cells_bound _ _ _ _ SA') as BA_. pose proof (rw_cells_bound _ _ _ _ SB') as BB_. cbn [cells_size csize Nat.add] in BA_, BB_.
    assert (PT0 : hide ((0 < Z.of_nat (bn_top ba))%Z -> bn_top bb = bn_top ba -> PTRS)).
    { apply hide_intro. intros HT ET. unfold PTRS.
      destruct (UDA HT) as (PA1 & PA2). destruct (UDB ltac:(rewrite ET; exact HT)) as (PB1 & PB2).
      assert (NEa : lbytes la <> []) by (destruct la; [cbn [length] in LLA; clear - LLA HT; lia | cbn; discriminate]).
      assert (NEb : lbytes lb <> []) by (destruct lb; [cbn [length] in LLB; rewrite ET in LLB; clear - LLB HT; lia | cbn; discriminate]).
      pose proof (bytes_at_below bgusegs m Da (lbytes la) MI0 RA NEa) as TA.
      pose proof (bytes_at_below bgusegs m Db (lbytes lb) MI0 RB NEb) as TB.
      rewrite lbytes_lengthZ in TA, TB. rewrite LLA in TA. rewrite LLB, ET in TB. unfold UTOP in TA, TB.
      repeat (split; [assumption|]). assumption. }
    carve_frame 16%nat STK.
    do 4 zstep.
    zstep.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K A0; lia|]. clear K.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K B0; lia|]. clear K.
    do 2 zstep.
    rewrite (lor_land7 A B (hide_elim _ UA) (hide_elim _ UB)).
    chk_lit.
    zstep. rewrite (sx32_small (Z.b2z (bn_neg ba))) by (clear - NA; lia).
    zstep. rewrite (sx32_small (Z.b2z (bn_neg bb))) by (clear - NB; lia).
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 gtv) ltac:(unfold gtv; destruct (bn_neg ba); apply Z_to_bv_eqm; vm_compute; reflexivity).
    assert (I : BINV m1).
    { unfold BINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; rewrite LLA; clear - SEPDA; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LLB; clear - SEPDB; lia].
      - split; [unfold bn_cells, wz; exact SA'|]. split; [unfold bn_cells, wz; exact SB'|]. split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU|]. split; [exact WM | exact LO]. }
    zstep. if_cases K; zify_cond K.
    { (* [comment removed for export] *)
      eapply bc_ret; [exact I|]. unfold cmp_pure, gtv.
      replace (Bool.eqb (bn_neg ba) (bn_neg bb)) with false by (clear - K; destruct (bn_neg ba), (bn_neg bb); cbn in *; congruence).
      reflexivity. }
    assert (EN : Bool.eqb (bn_neg ba) (bn_neg bb) = true) by (clear - K; destruct (bn_neg ba), (bn_neg bb); cbn in *; congruence).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - TA31; lia).
    zstep. rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - TB31; lia).
    zstep. rewrite lts_small by (clear - TA31 TB31; lia). if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      eapply bc_ret; [exact I|]. unfold cmp_pure. rewrite EN. cbn [negb]. cbv zeta.
      replace (bn_top bb <? bn_top ba)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K1; lia). reflexivity. }
    do 3 zstep.
    setreg 14%Z (Z_to_bv 64 ltv) ltac:(unfold ltv; destruct (bn_neg ba); apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep. rewrite lts_small by (clear - TA31 TB31; lia). if_cases K2; zify_cond K2.
    2:{ (* [comment removed for export] *)
      do 2 zstep. eapply bc_ret; [exact I|]. unfold cmp_pure. rewrite EN. cbn [negb]. cbv zeta.
      replace (bn_top bb <? bn_top ba)%nat with false by (symmetry; apply Nat.ltb_ge; clear - K1; lia).
      replace (bn_top ba <? bn_top bb)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K2; lia). reflexivity. }
    assert (ET : bn_top bb = bn_top ba) by (clear - K1 K2; lia).
    (* [comment removed for export] *)
    zstep. rewrite (bn_swrap32_small (Z.of_nat (bn_top ba) + -1)) by (clear - TA31; lia).
    zstep. rewrite lts_signed by (clear - TA31; lia). if_cases C; [exfalso; zify_cond C; clear - C; lia | clear C].
    zstep. rewrite lts_signed by (clear - TA31; lia). if_cases K3; zify_cond K3.
    { (* [comment removed for export] *)
      eapply bc_zero; [exact I|]. rewrite (cmp_pure_tops_eq EN ET).
      assert (T0 : bn_top ba = 0%nat) by (clear - K3; lia). rewrite ET, T0. reflexivity. }
    assert (PT : PTRS).
    { apply hide_elim in PT0. apply PT0; [clear - K3; lia | exact ET]. }
    zstep. zstep.
    replace (Z.land Da 18446744073709551615) with Da
      by (symmetry; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; clear - PT; unfold PTRS in PT; lia).
    replace (0 <? Da)%Z with true by (symmetry; apply Z.ltb_lt; clear - PT; unfold PTRS in PT; lia).
    change (Z.b2z true) with 1%Z.
    assert (EK : exists k, bn_top ba = S k) by (clear - K3; destruct (bn_top ba); [exfalso; lia | eexists; reflexivity]).
    destruct EK as (k & EK).
    setreg 13%Z (Z_to_bv 64 (Z.of_nat (S k))) ltac:(rewrite EK; reflexivity).
    eapply bc_loop; [exact I | exact PT | rewrite EK; clear; lia | exact EN | exact ET |].
    rewrite <- EK, ET, !firstn_firstn, Nat.min_id. reflexivity.
  Qed.
End Proofs.
