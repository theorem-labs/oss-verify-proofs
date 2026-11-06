(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require W_cmp_words.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop BnRepDefs AsStruct W_smallA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition BN_UCMP : Z := 0x1f54c0.

Notation ro_post := W_cmp_words.ro_post.

(* [comment removed for export] *)
Lemma limbs_at_47 : forall m D (l : list Z), limbs_at asegs m D l -> mem_inv asegs m -> (0 < length l)%nat ->
  (0 <= D /\ D + 8 * Z.of_nat (length l) <= 140737488355328)%Z.
Proof.
  intros m D l H MI Hl. pose proof (limbs_at_bound _ _ _ _ H) as BA.
  assert (NE : lbytes l <> []).
  { intros E. pose proof (lbytes_lengthZ l) as L. rewrite E in L. cbn [length] in L. lia. }
  pose proof (bytes_at_below asegs m D _ MI H NE) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA. lia.
Qed.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo A B Da Db : Z) (ba bb : bignum bptr).
  Notation SP := (bv_unsigned sp).
  Notation la := (firstn (bn_top ba) (bn_buf ba)).
  Notation lb := (firstn (bn_top bb) (bn_buf bb)).
  Hypothesis OKA : bn_okm ba.
  Hypothesis OKB : bn_okm bb.
  Hypothesis A0 : (0 < A)%Z.
  Hypothesis B0 : (0 < B)%Z.
  Hypothesis LO : (lo <= SP - 48)%Z.
  Hypothesis SEPA : (A + 24 <= SP - 48 \/ SP <= A)%Z.
  Hypothesis SEPB : (B + 24 <= SP - 48 \/ SP <= B)%Z.
  Hypothesis SEPDA : (Da + 8 * Z.of_nat (bn_top ba) <= SP - 48 \/ SP <= Da)%Z.
  Hypothesis SEPDB : (Db + 8 * Z.of_nat (bn_top bb) <= SP - 48 \/ SP <= Db)%Z.
  Hypothesis ALA : (A mod 8 = 0)%Z.
  Hypothesis ALB : (B mod 8 = 0)%Z.
  Hypothesis ALDA : (Da mod 8 = 0)%Z.
  Hypothesis ALDB : (Db mod 8 = 0)%Z.
  Hypothesis SLO : (SHHI <= lo)%Z.

  Notation POST := (ro_post asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 48%Z (ucmp_pure ba bb) lo m).

  (* [comment removed for export] *)
  Notation ST pc mm x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition UINV (m1 : word -> option byte) : Prop :=
    limbs_at asegs m1 Da la /\ limbs_at asegs m1 Db lb /\
    acc asegs m1 Da (8 * Z.of_nat (bn_top ba)) /\ acc asegs m1 Db (8 * Z.of_nat (bn_top bb)) /\
    (exists jb, rw_cells asegs m1 (SP + -48) [CB 16 jb; C8 s2; C8 s1; C8 s0; C8 ra]) /\ stk asegs m1 lo (SP + -48) /\
    mem_inv asegs m1 /\ munch [(SP + -48, SP)]%Z m m1 /\ wmono asegs m m1.

  (* [comment removed for export] *)
  Lemma uc_ret : forall m1 res x8 x11 x12 x13 x14 x15 x16 x17, UINV m1 -> res = ucmp_pure ba bb ->
    evt asegs POST (ST 0x1f57b8 m1 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 res x8 x11 x12 x13 x14 x15 x16 x17 (HA & HB & _ & _ & (jb & FR) & ST & MI & MU & WM) ->.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma uc_zero : forall m1 x8 x10 x11 x12 x13 x14 x15 x16 x17, UINV m1 -> ucmp_pure ba bb = 0%Z ->
    evt asegs POST (ST 0x1f57d0 m1 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    do 2 zstep.
    eapply uc_ret; [exact I | symmetry; exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma uc_differ : forall m1 x y x8 x10 x11 x12 x13 x14 x15, UINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = ucmp_pure ba bb ->
    evt asegs POST (ST 0x1f55ec m1 x8 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 x) (Z_to_bv 64 y)).
  Proof.
    intros m1 x y x8 x10 x11 x12 x13 x14 x15 I Rx Ry NE E.
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep.
    eapply uc_ret; [exact I | exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma uc_loop : forall (k : nat) m1 x8 x16 x17, UINV m1 -> (k <= bn_top ba)%nat -> bn_top bb = bn_top ba ->
    ucmp_pure ba bb = cmp_words (firstn k la) (firstn k lb) ->
    evt asegs POST (ST 0x1f55a8 m1 x8 (Z_to_bv 64 (Da + 8 * Z.of_nat k + -8)) (Z_to_bv 64 (Db + 8 * Z.of_nat k + -8))
                       (Z_to_bv 64 (Z.of_nat k + 1)) (Z_to_bv 64 SHB)
                       (Z_to_bv 64 (Db + 8 * Z.of_nat k + -8)) (Z_to_bv 64 (Da + 8 * Z.of_nat k + -8)) x16 x17).
  Proof.
    induction k as [|k IH]; intros m1 x8 x16 x17 I Hk ET E.
    - zstep. zstep. if_cases K; zify_cond K.
      + eapply uc_zero; [exact I | rewrite E; reflexivity].
      + exfalso. clear - K. lia.
    - pose proof I as (HA & HB & ACDA & ACDB & _ & _ & MI & _).
      pose proof OKA as (LMA & TDA & DMA & _). pose proof OKB as (LMB & TDB & DMB & _).
      assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
      assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
      assert (LLB : length lb = bn_top ba) by (rewrite firstn_length_le; [exact ET | clear - TDB ET; unfold bn_dmax in *; lia]).
      pose proof (limbs_at_47 m1 Da la HA MI ltac:(rewrite LLA; clear - Hk; lia)) as BDA. rewrite LLA in BDA.
      pose proof (limbs_at_47 m1 Db lb HB MI ltac:(rewrite LLB; clear - Hk; lia)) as BDB. rewrite LLB in BDB.
      rewrite ET in ACDB.
      destruct (nth_error la k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; exfalso; clear - Ex LLA Hk; lia].
      destruct (nth_error lb k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; exfalso; clear - Ey LLB Hk; lia].
      pose proof (limbs_nth_error_lit la k x (limbs_firstn _ _ LMA) Ex) as Rx.
      pose proof (limbs_nth_error_lit lb k y (limbs_firstn _ _ LMB) Ey) as Ry.
      pose proof (munch_refl (@nil (Z * Z)) m1) as MU0.
      zstep.
      rewrite (bn_swrap32_small (Z.of_nat (S k) + 1 + -1)) by (clear - Hk TA31; lia).
      replace (Z.of_nat (S k) + 1 + -1)%Z with (Z.of_nat (S k)) by (clear; lia).
      zstep. if_cases K; zify_cond K;
        [exfalso; apply andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; clear - K Hk TA31; lia|].
      do 2 zstep.
      (let ad := cur_mem_addr in
       pose proof (acc_rd_limb asegs [] m1 m1 Da (Z.of_nat (bn_top ba)) 0 (Z.of_nat k) ad ACDA MU0 Logic.I ALDA BDA eq_refl ltac:(lia) ltac:(lia)
                     ltac:(clear - Hk; lia) ltac:(sh_addr_k)) as RD); zstep; clear RD.
      chk0.
      do 2 zstep.
      (let ad := cur_mem_addr in
       pose proof (acc_rd_limb asegs [] m1 m1 Db (Z.of_nat (bn_top ba)) 0 (Z.of_nat k) ad ACDB MU0 Logic.I ALDB BDB eq_refl ltac:(lia) ltac:(lia)
                     ltac:(clear - Hk; lia) ltac:(sh_addr_k)) as RD); zstep; clear RD.
      chk0.
      (let ad := cur_mem_addr in pose proof (limbs_at_read_nth asegs m1 Da la k x ad HA Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
      (let ad := cur_mem_addr in pose proof (limbs_at_read_nth asegs m1 Db lb k y ad HB Ey ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
      do 4 zstep.
      pose proof (cmp_words_top la lb k x y ltac:(rewrite LLA, LLB; reflexivity) Ex Ey) as T.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (E' : ucmp_pure ba bb = cmp_words (firstn k la) (firstn k lb)).
        { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
        setreg 10%Z (Z_to_bv 64 (Da + 8 * Z.of_nat k + -8)) ltac:(f_equal; clear; lia).
        setreg 11%Z (Z_to_bv 64 (Db + 8 * Z.of_nat k + -8)) ltac:(f_equal; clear; lia).
        setreg 12%Z (Z_to_bv 64 (Z.of_nat k + 1)) ltac:(f_equal; clear; lia).
        eapply IH; [exact I | clear - Hk; lia | exact ET | exact E'].
      + eapply uc_differ; [exact I | exact Rx | exact Ry | exact K2 |].
        rewrite E, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
  Qed.

  Lemma BN_ucmp_specA :
    rw_cells asegs m A (bn_cells Da ba) -> rw_cells asegs m B (bn_cells Db bb) ->
    limbs_at asegs m Da la -> limbs_at asegs m Db lb ->
    stk asegs m lo SP -> mem_inv asegs m ->
    shb_cells asegs 5932248 6753336 m -> acc asegs m A 24 -> acc asegs m B 24 ->
    acc asegs m Da (8 * Z.of_nat (bn_top ba)) -> acc asegs m Db (8 * Z.of_nat (bn_top bb)) ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 B ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BN_UCMP) fc None m (seg_rom asegs)).
  Proof.
    intros SA SB RA RB STK MI0 (SHB1 & SHB2) ACA ACB ACDA ACDB EA0 EA1.
    unfold BN_UCMP. subst a0 a1. unfold SHLO, SHHI in *. pose proof MI0 as MI0'. apply hide_intro in MI0'.
    pose proof (munch_refl [(SP - 48, SP)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (OFF : offshW [(SP - 48, SP)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
    pose proof (bn_cells_bound47 m A _ SA MI0 ltac:(cbn; lia)) as A47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in A47.
    pose proof (bn_cells_bound47 m B _ SB MI0 ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
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
    apply (flag_cell_split asegs m A _ _ _ _ (bn_flags ba) FRA) in SA.
    apply (flag_cell_split asegs m B _ _ _ _ (bn_flags bb) FRB) in SB.
    carve_frame 48%nat STK.
    do 6 step.
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K A0; lia|]. clear K.
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K B0; lia|]. clear K.
    do 3 step.
    do 2 step. shl. chk0.
    do 2 step. shl. chk0.
    step. do 3 step. shl. step. chk0.
    step. rewrite (zxb_small (bn_flags ba)) by (clear - FRA; lia). step.
    rewrite (unsigned_lit (bn_flags ba)) by (clear - FRA; lia). rewrite EL4A. step. if_false.
    do 3 step. shl. chk0.
    step. rewrite (zxb_small (bn_flags bb)) by (clear - FRB; lia). step.
    rewrite (unsigned_lit (bn_flags bb)) by (clear - FRB; lia). rewrite EL4B. step. if_false.
    do 3 step. shl. chk0.
    do 3 step. shl. step. chk0.
    step.
    rewrite (zx32_small (Z.of_nat (bn_top ba))) by (clear - TA31; lia).
    rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - TB31; lia).
    assert (UI : UINV m1).
    { unfold UINV. split; [|split; [|split; [|split]]].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; rewrite LLA; clear - SEPDA; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LLB; clear - SEPDB; lia].
      - destruct (Nat.eq_dec (bn_top ba) 0) as [E0|N0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia|].
        pose proof (limbs_at_47 m Da la RA (hide_elim _ MI0') ltac:(rewrite LLA; clear - N0; lia)) as BD. rewrite LLA in BD.
        eapply (acc_munch asegs _ m m1 Da _ ACDA MU OFF); lia.
      - destruct (Nat.eq_dec (bn_top bb) 0) as [E0|N0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia|].
        pose proof (limbs_at_47 m Db lb RB (hide_elim _ MI0') ltac:(rewrite LLB; clear - N0; lia)) as BD. rewrite LLB in BD.
        eapply (acc_munch asegs _ m m1 Db _ ACDB MU OFF); lia.
      - split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear RA RB FR STK MU WM.
    zstep. rewrite (bn_swrap32_small (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb))) by (clear - TA31 TB31; lia).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      eapply uc_ret; [exact UI|]. unfold ucmp_pure. cbv zeta.
      destruct (Z.eqb_spec (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb)) 0) as [E0|_]; [contradiction | reflexivity].
    - rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      assert (ET : bn_top bb = bn_top ba) by (clear - K; lia).
      do 7 zstep.
      setreg 10%Z (Z_to_bv 64 (Da + 8 * Z.of_nat (bn_top ba) + -8)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
      setreg 11%Z (Z_to_bv 64 (Db + 8 * Z.of_nat (bn_top ba) + -8)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
      eapply uc_loop; [exact UI | clear; lia | exact ET |].
      unfold ucmp_pure. cbv zeta. rewrite K. cbn [Z.eqb].
      rewrite ET, !firstn_firstn, Nat.min_id. reflexivity.
  Qed.

End Proofs.
