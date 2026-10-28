(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require W_cmp_words.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import BnRepDefs AsStruct W_smallA W_ucmpA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2034336 => 1
  | 2034340 => 1
  | 2034344 => 2
  | 2034536 => 2
  | 2034568 => 1
  | 2034588 => 2
  | 2034592 => 1
  | 2034596 => 1
  | 2034600 => 2
  | 2034604 => 2
  | 2034608 => 1
  | 2034612 => 2
  | 2034648 => 2
  | 2034652 => 1
  | 2034656 => 1
  | 2034660 => 1
  | 2034664 => 2
  | 2034668 => 2
  | 2034672 => 1
  | 2034676 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition BN_CMP : Z := 0x1f0a84.

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
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (A + 24 <= SP - 16 \/ SP <= A)%Z.
  Hypothesis SEPB : (B + 24 <= SP - 16 \/ SP <= B)%Z.
  Hypothesis SEPDA : (Da + 8 * Z.of_nat (bn_top ba) <= SP - 16 \/ SP <= Da)%Z.
  Hypothesis SEPDB : (Db + 8 * Z.of_nat (bn_top bb) <= SP - 16 \/ SP <= Db)%Z.
  Hypothesis ALA : (A mod 8 = 0)%Z.
  Hypothesis ALB : (B mod 8 = 0)%Z.
  Hypothesis ALDA : (Da mod 8 = 0)%Z.
  Hypothesis ALDB : (Db mod 8 = 0)%Z.
  Hypothesis SLO : (SHHI <= lo)%Z.

  Notation POST := (ro_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_pure ba bb) lo m).

  Definition gtv : Z := if bn_neg ba then -1 else 1.
  Definition ltv : Z := if bn_neg ba then 1 else -1.

  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition BINV (m1 : word -> option byte) : Prop :=
    limbs_at bsegs m1 Da la /\ limbs_at bsegs m1 Db lb /\
    rw_cells bsegs m1 A (bn_cells Da ba) /\ rw_cells bsegs m1 B (bn_cells Db bb) /\
    acc bsegs m1 A 24 /\ acc bsegs m1 B 24 /\
    acc bsegs m1 Da (8 * Z.of_nat (bn_top ba)) /\ acc bsegs m1 Db (8 * Z.of_nat (bn_top bb)) /\
    rw_cells bsegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bsegs m1 lo (SP + -16) /\
    mem_inv bsegs m1 /\ munch [(SP + -16, SP)]%Z m m1 /\ wmono bsegs m m1.

  (* [comment removed for export] *)
  Lemma bc_ret : forall m1 res x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 x29, BINV m1 -> res = cmp_pure ba bb ->
    evt bsegs POST (ST 0x1f0b54 m1 x5 x6 x7 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x28 x29).
  Proof.
    intros m1 res x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 x29 (HA & HB & _ & _ & _ & _ & _ & _ & FR & ST & MI & MU & WM) ->.
    do 2 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma bc_zero : forall m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29, BINV m1 -> cmp_pure ba bb = 0%Z ->
    evt bsegs POST (ST 0x1f0c1c m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29).
  Proof.
    intros m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 I E.
    do 2 zstep.
    eapply bc_ret; [exact I | symmetry; exact E].
  Qed.

  Lemma cmp_pure_tops_eq : Bool.eqb (bn_neg ba) (bn_neg bb) = true -> bn_top bb = bn_top ba ->
    cmp_pure ba bb = (if cmp_words la lb =? 0 then 0 else if 0 <? cmp_words la lb then gtv else ltv)%Z.
  Proof.
    intros EN ET. unfold cmp_pure, gtv, ltv. rewrite EN. cbn [negb]. cbv zeta. rewrite ET, Nat.ltb_irrefl. reflexivity.
  Qed.

  Definition PTRS : Prop :=
    (0 < Da /\ Da + 8 * Z.of_nat (bn_top ba) <= 140737488355328 /\
     0 < Db /\ Db + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z.

  (* [comment removed for export] *)
  Lemma bc_loop : forall (k : nat) m1 x7 x8 x12 x13 x28 x29, BINV m1 -> PTRS -> (S k <= bn_top ba)%nat ->
    Bool.eqb (bn_neg ba) (bn_neg bb) = true -> bn_top bb = bn_top ba ->
    cmp_words la lb = cmp_words (firstn (S k) la) (firstn (S k) lb) ->
    evt bsegs POST (ST 0x1f0b90 m1 (Z_to_bv 64 1) (Z_to_bv 64 (shad B)) x7 x8 (Z_to_bv 64 gtv) (Z_to_bv 64 B) x12 x13
                       (Z_to_bv 64 ltv) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat (S k))) (Z_to_bv 64 Da) x28 x29).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros m1 x7 x8 x12 x13 x28 x29 I PT Hk EN ET E.
    pose proof I as (HA & HB & SA1 & SB1 & ACA & ACB & ACDA & ACDB & _ & _ & MI & _).
    pose proof (bn_cells_bound47 m1 B _ SB1 MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
    unfold bn_cells, wz in SA1, SB1.
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
    assert (PA : (0 < Da /\ Da + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z) by (clear - PT; unfold PTRS in PT; tauto).
    assert (PB : (0 < Db /\ Db + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z) by (clear - PT; unfold PTRS in PT; tauto).
    assert (Hk' : (Z.of_nat k < Z.of_nat (bn_top ba))%Z) by (clear - Hk; lia).
    zstep.
    rewrite (bn_swrap32_small (Z.of_nat (S k) + -1)) by (clear - Hk TA31; lia).
    replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by (clear; lia).
    do 2 zstep.
    rewrite (Z.shiftl_mul_pow2 (Z.of_nat k) 3) by (clear; lia). change (2 ^ 3)%Z with 8%Z.
    ub. do 2 zstep.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bsegs [] m1 m1 Da (Z.of_nat (bn_top ba)) 0 (Z.of_nat k) ad ACDA MU0 Logic.I ALDA BDA eq_refl ltac:(lia) ltac:(lia)
                   ltac:(clear - Hk; lia) ltac:(sh_addr_k)) as RD); zstep; clear RD.
    chk0.
      (* [comment removed for export] *)
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bsegs [] m1 m1 B 3 0 0 ad ACB MU0 Logic.I ALB ltac:(clear - B47; lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(unfold wa; f_equal; f_equal; clear; lia)) as RD); zstep; clear RD.
    chk0.
    zstep. zstep.
    ub. do 2 zstep.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bsegs [] m1 m1 Db (Z.of_nat (bn_top ba)) 0 (Z.of_nat k) ad ACDB MU0 Logic.I ALDB BDB eq_refl ltac:(lia) ltac:(lia)
                   ltac:(clear - Hk; lia) ltac:(sh_addr_k)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bsegs m1 Da la k x ad HA Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bsegs m1 Db lb k y ad HB Ey ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top la lb k x y ltac:(rewrite LLA, LLB; reflexivity) Ex Ey) as T.
    zstep. if_cases K2; zify_cond K2.
    {
      eapply bc_ret; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E, T. unfold cmp1.
      destruct (Z.eqb_spec x y) as [E0|_]; [exfalso; clear - E0 K2; lia|].
      replace (y <? x)%Z with true by (symmetry; apply Z.ltb_lt; exact K2). reflexivity. }
    zstep. if_cases K3; zify_cond K3.
    {
      do 2 zstep.
      eapply bc_ret; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E, T. unfold cmp1.
      destruct (Z.eqb_spec x y) as [E0|_]; [exfalso; clear - E0 K3; lia|].
      replace (y <? x)%Z with false by (symmetry; apply Z.ltb_ge; clear - K2; lia). reflexivity. }
      (* [comment removed for export] *)
    assert (Exy : x = y) by (clear - K2 K3; lia). (* [comment removed for export] *) (* [comment removed for export] *) (* [comment removed for export] *)
    assert (E' : cmp_words la lb = cmp_words (firstn k la) (firstn k lb)).
    { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
    zstep. rewrite lts_small by (clear - Hk TA31; lia). if_cases K4; zify_cond K4.
    - destruct k as [|k']; [exfalso; clear - K4; lia|].
      eapply (IH k'); [clear; lia | exact I | exact PT | clear - Hk; lia | exact EN | exact ET | exact E'].
    - assert (K0 : k = 0%nat) by (clear - K4; lia). subst k.
      eapply bc_zero; [exact I|]. rewrite (cmp_pure_tops_eq EN ET), E'. reflexivity.
  Qed.

  Lemma BN_cmp_specA :
    rw_cells bsegs m A (bn_cells Da ba) -> rw_cells bsegs m B (bn_cells Db bb) ->
    limbs_at bsegs m Da la -> limbs_at bsegs m Db lb ->
    stk bsegs m lo SP -> mem_inv bsegs m ->
    shb_cells bsegs 6163672 6961656 m -> acc bsegs m A 24 -> acc bsegs m B 24 ->
    acc bsegs m Da (8 * Z.of_nat (bn_top ba)) -> acc bsegs m Db (8 * Z.of_nat (bn_top bb)) ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 B ->
    ub_ptr_ok (Z.of_nat (bn_top ba)) Da -> ub_ptr_ok (Z.of_nat (bn_top bb)) Db ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BN_CMP) fc None m (seg_rom bsegs)).
  Proof.
    intros SA SB RA RB STK MI0 (SHB1 & SHB2) ACA ACB ACDA ACDB EA0 EA1 UDA UDB.
    unfold BN_CMP. subst a0 a1. unfold SHLO, SHHI in *. pose proof MI0 as MI0'. apply hide_intro in MI0'.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (OFF : offshW [(SP - 16, SP)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
    pose proof (bn_cells_bound47 m A _ SA MI0 ltac:(cbn; lia)) as A47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in A47.
    pose proof (bn_cells_bound47 m B _ SB MI0 ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
    unfold bn_cells in SA, SB.
    pose proof OKA as (LMA & TDA & DMA & FLA). pose proof OKB as (LMB & TDB & DMB & FLB).
    assert (TA31 : (0 <= Z.of_nat (bn_top ba) < 8388608)%Z) by (clear - TDA DMA; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (TB31 : (0 <= Z.of_nat (bn_top bb) < 8388608)%Z) by (clear - TDB DMB; unfold BN_WORDS_MAX, bn_dmax in *; lia).
    assert (LLA : length la = bn_top ba) by (rewrite firstn_length_le; [reflexivity | clear - TDA; unfold bn_dmax in *; lia]).
    assert (LLB : length lb = bn_top bb) by (rewrite firstn_length_le; [reflexivity | clear - TDB; unfold bn_dmax in *; lia]).
    assert (NA : (0 <= Z.b2z (bn_neg ba) <= 1)%Z) by (destruct (bn_neg ba); cbn; lia).
    assert (NB : (0 <= Z.b2z (bn_neg bb) <= 1)%Z) by (destruct (bn_neg bb); cbn; lia).
    assert (PT0 : hide ((0 < Z.of_nat (bn_top ba))%Z -> bn_top bb = bn_top ba -> PTRS)).
    { apply hide_intro. intros HT ET. unfold PTRS.
      destruct (UDA HT) as (PA1 & _). destruct (UDB ltac:(rewrite ET; exact HT)) as (PB1 & _).
      pose proof (limbs_at_47 m Da la RA MI0 ltac:(rewrite LLA; clear - HT; lia)) as BD1. rewrite LLA in BD1.
      pose proof (limbs_at_47 m Db lb RB MI0 ltac:(rewrite LLB, ET; clear - HT; lia)) as BD2. rewrite LLB, ET in BD2.
      clear - PA1 PB1 BD1 BD2. lia. }
    clear UDA UDB.
    unfold wz in SA, SB.
    carve_frame 16%nat STK.
    do 4 step. step.
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K A0; lia|]. clear K.
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K B0; lia|]. clear K.
    ub; do 3 step.
    do 3 step. shl. chk0.
    do 3 step. shl. step. chk0.
    step.
    rewrite (sx32_small (Z.b2z (bn_neg ba))) by (clear - NA; lia).
    rewrite (sx32_small (Z.b2z (bn_neg bb))) by (clear - NB; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (BI : BINV m1).
    { unfold BINV. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; rewrite LLA; clear - SEPDA; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LLB; clear - SEPDB; lia].
      - unfold bn_cells, wz. exact SA.
      - unfold bn_cells, wz. exact SB.
      - eapply (acc_munch bsegs _ m m1 A _ ACA MU OFF); lia.
      - eapply (acc_munch bsegs _ m m1 B _ ACB MU OFF); lia.
      - destruct (Nat.eq_dec (bn_top ba) 0) as [E0|N0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia|].
        pose proof (limbs_at_47 m Da la RA (hide_elim _ MI0') ltac:(rewrite LLA; clear - N0; lia)) as BD. rewrite LLA in BD.
        eapply (acc_munch bsegs _ m m1 Da _ ACDA MU OFF); lia.
      - destruct (Nat.eq_dec (bn_top bb) 0) as [E0|N0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia|].
        pose proof (limbs_at_47 m Db lb RB (hide_elim _ MI0') ltac:(rewrite LLB; clear - N0; lia)) as BD. rewrite LLB in BD.
        eapply (acc_munch bsegs _ m m1 Db _ ACDB MU OFF); lia.
      - split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 gtv) ltac:(unfold gtv; destruct (bn_neg ba); apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep. if_cases K; zify_cond K.
    { (* [comment removed for export] *)
      eapply bc_ret; [exact BI|]. unfold cmp_pure, gtv.
      replace (Bool.eqb (bn_neg ba) (bn_neg bb)) with false by (clear - K; destruct (bn_neg ba), (bn_neg bb); cbn in *; congruence).
      reflexivity. }
    assert (EN : Bool.eqb (bn_neg ba) (bn_neg bb) = true) by (clear - K; destruct (bn_neg ba), (bn_neg bb); cbn in *; congruence).
    do 3 step. shl. chk0.
    do 3 step. shl. step. chk0.
    step.
    rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - TA31; lia).
    rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - TB31; lia).
    zstep. rewrite lts_small by (clear - TA31 TB31; lia). if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      eapply bc_ret; [exact BI|]. unfold cmp_pure. rewrite EN. cbn [negb]. cbv zeta.
      replace (bn_top bb <? bn_top ba)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K1; lia). reflexivity. }
    do 3 zstep.
    setreg 14%Z (Z_to_bv 64 ltv) ltac:(unfold ltv; destruct (bn_neg ba); apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep. rewrite lts_small by (clear - TA31 TB31; lia). if_cases K2; zify_cond K2.
    2:{ (* [comment removed for export] *)
      do 2 zstep. eapply bc_ret; [exact BI|]. unfold cmp_pure. rewrite EN. cbn [negb]. cbv zeta.
      replace (bn_top bb <? bn_top ba)%nat with false by (symmetry; apply Nat.ltb_ge; clear - K1; lia).
      replace (bn_top ba <? bn_top bb)%nat with true by (symmetry; apply Nat.ltb_lt; clear - K2; lia). reflexivity. }
    assert (ET : bn_top bb = bn_top ba) by (clear - K1 K2; lia).

    zstep. rewrite (bn_swrap32_small (Z.of_nat (bn_top ba) + -1)) by (clear - TA31; lia).
    ub; zstep. rewrite lts_signed by (clear - TA31; lia). if_cases K3; zify_cond K3.
    {
      eapply bc_zero; [exact BI|]. rewrite (cmp_pure_tops_eq EN ET).
      assert (T0 : bn_top ba = 0%nat) by (clear - K3; lia). rewrite ET, T0. reflexivity. }
    assert (PT : PTRS).
    { apply hide_elim in PT0. apply PT0; [clear - K3; lia | exact ET]. }
    do 2 step. shl. chk0.
    step.
    step. ub; step.
    replace (Z.land Da 18446744073709551615) with Da
      by (symmetry; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; clear - PT; unfold PTRS in PT; lia).
    replace (0 <? Da)%Z with true by (symmetry; apply Z.ltb_lt; clear - PT; unfold PTRS in PT; lia).
    change (Z.b2z true) with 1%Z.
    assert (EK : exists k, bn_top ba = S k) by (clear - K3; destruct (bn_top ba); [exfalso; lia | eexists; reflexivity]).
    destruct EK as (k & EK).
    setreg 6%Z (Z_to_bv 64 (shad B)) ltac:(f_equal; unfold shad; rewrite ?unsigned_lit by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    setreg 16%Z (Z_to_bv 64 (Z.of_nat (S k))) ltac:(rewrite EK; reflexivity).
    eapply bc_loop; [exact BI | exact PT | rewrite EK; clear; lia | exact EN | exact ET |].
    rewrite <- EK, ET, !firstn_firstn, Nat.min_id. reflexivity.
  Qed.
End Proofs.
