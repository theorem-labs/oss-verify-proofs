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
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import BnRepDefs AsStruct W_smallA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2033116 => 1
  | 2033120 => 2
  | 2033152 => 1
  | 2033156 => 2
  | 2033300 => 1
  | 2033304 => 2
  | 2033320 => 2
  | 2033328 => 1
  | 2033332 => 1
  | 2033348 => 2
  | 2033352 => 1
  | 2033356 => 1
  | 2033360 => 2
  | 2033364 => 2
  | 2033368 => 1
  | 2033372 => 2
  | 2033396 => 2
  | 2033400 => 1
  | 2033404 => 1
  | 2033408 => 2
  | 2033412 => 2
  | 2033416 => 1
  | 2033420 => 2
  | 2033548 => 1
  | 2033552 => 1
  | 2033556 => 1
  | 2033560 => 1
  | 2033580 => 2
  | 2033584 => 1
  | 2033588 => 1
  | 2033592 => 2
  | 2033596 => 2
  | 2033616 => 2
  | 2033620 => 1
  | 2033624 => 1
  | 2033628 => 2
  | 2033632 => 2
  | 2033820 => 1
  | 2033824 => 2
  | 2033828 => 1
  | 2033832 => 1
  | 2033836 => 1
  | 2033840 => 1
  | 2033844 => 2
  | 2033848 => 2
  | 2033960 => 1
  | 2033964 => 2
  | 2033968 => 1
  | 2033972 => 1
  | 2033976 => 1
  | 2033980 => 1
  | 2033984 => 2
  | 2033988 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition BN_UCMP : Z := 0x1f05a8.

Notation ro_post := W_cmp_words.ro_post.

(* [comment removed for export] *)
Lemma limbs_at_47 : forall m D (l : list Z), limbs_at bsegs m D l -> mem_inv bsegs m -> (0 < length l)%nat ->
  (0 <= D /\ D + 8 * Z.of_nat (length l) <= 140737488355328)%Z.
Proof.
  intros m D l H MI Hl. pose proof (limbs_at_bound _ _ _ _ H) as BA.
  assert (NE : lbytes l <> []).
  { intros E. pose proof (lbytes_lengthZ l) as L. rewrite E in L. cbn [length] in L. lia. }
  pose proof (bytes_at_below bsegs m D _ MI H NE) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA. lia.
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
  Hypothesis LO : (lo <= SP - 80)%Z.
  Hypothesis SEPA : (A + 24 <= SP - 80 \/ SP <= A)%Z.
  Hypothesis SEPB : (B + 24 <= SP - 80 \/ SP <= B)%Z.
  Hypothesis SEPDA : (Da + 8 * Z.of_nat (bn_top ba) <= SP - 80 \/ SP <= Da)%Z.
  Hypothesis SEPDB : (Db + 8 * Z.of_nat (bn_top bb) <= SP - 80 \/ SP <= Db)%Z.
  Hypothesis ALA : (A mod 8 = 0)%Z.
  Hypothesis ALB : (B mod 8 = 0)%Z.
  Hypothesis ALDA : (Da mod 8 = 0)%Z.
  Hypothesis ALDB : (Db mod 8 = 0)%Z.
  Hypothesis SLO : (SHHI <= lo)%Z.

  Notation POST := (ro_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80%Z (ucmp_pure ba bb) lo m).

  (* [comment removed for export] *)
  Notation ST pc mm x5 x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition UINV (m1 : word -> option byte) : Prop :=
    limbs_at bsegs m1 Da la /\ limbs_at bsegs m1 Db lb /\
    acc bsegs m1 Da (8 * Z.of_nat (bn_top ba)) /\ acc bsegs m1 Db (8 * Z.of_nat (bn_top bb)) /\
    (exists jb, rw_cells bsegs m1 (SP + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\ stk bsegs m1 lo (SP + -80) /\
    mem_inv bsegs m1 /\ munch [(SP + -80, SP)]%Z m m1 /\ wmono bsegs m m1.

  (* [comment removed for export] *)
  Lemma uc_ret : forall m1 res x5 x8 x10 x11 x12 x13 x14 x15 x17, UINV m1 -> res = ucmp_pure ba bb ->
    (-2147483648 <= res < 2147483648)%Z ->
    evt bsegs POST (ST 0x1f0994 m1 x5 x8 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 res) x17).
  Proof.
    intros m1 res x5 x8 x10 x11 x12 x13 x14 x15 x17 (HA & HB & _ & _ & (jb & FR) & ST & MI & MU & WM) -> RR.
    zstep.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by (clear; lia).
    change (2 ^ 64)%Z with 18446744073709551616%Z. rewrite (bn_swrap32_mod (ucmp_pure ba bb) 0) by (clear - RR; lia). rewrite Z.add_0_r.
    do 9 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. zstep.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma uc_zero : forall m1 x5 x8 x10 x11 x12 x13 x14 x15 x16 x17, UINV m1 -> ucmp_pure ba bb = 0%Z ->
    evt bsegs POST (ST 0x1f0730 m1 x5 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    do 2 zstep.
    eapply uc_ret; [exact I | symmetry; exact E | clear; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma uc_differ : forall m1 x y x5 x8 x12 x13 x14 x15 x16 x17, UINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = ucmp_pure ba bb ->
    evt bsegs POST (ST 0x1f09c4 m1 x5 x8 (Z_to_bv 64 x) (Z_to_bv 64 y) x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x y x5 x8 x12 x13 x14 x15 x16 x17 I Rx Ry NE E.
    do 3 zstep.
    setreg 16%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    zstep.
    eapply uc_ret; [exact I | exact E |].
    unfold cmp1. destruct (x =? y)%Z; [clear; lia|]. destruct (y <? x)%Z; clear; lia.
  Qed.

  Definition PTRS : Prop :=
    (0 < Da /\ Da + 8 * Z.of_nat (bn_top ba) <= 140737488355328 /\
     0 < Db /\ Db + 8 * Z.of_nat (bn_top ba) <= 140737488355328)%Z.

  (* [comment removed for export] *)
  Lemma uc_loop : forall (k : nat) m1 x5 x8 x10 x11, UINV m1 -> PTRS -> (S k <= bn_top ba)%nat -> bn_top bb = bn_top ba ->
    ucmp_pure ba bb = cmp_words (firstn (S k) la) (firstn (S k) lb) ->
    evt bsegs POST (ST 0x1f06b8 m1 x5 x8 x10 x11 (Z_to_bv 64 (Z.of_nat (S k))) (Z_to_bv 64 SHB) (Z_to_bv 64 Db) (Z_to_bv 64 Da) (Z_to_bv 64 1) (Z_to_bv 64 1)).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros m1 x5 x8 x10 x11 I PT Hk ET E.
    pose proof I as (HA & HB & ACDA & ACDB & _ & _ & MI & _).
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
    do 2 zstep. (* [comment removed for export] *)
    rewrite (Z.shiftl_mul_pow2 (Z.of_nat k) 3) by (clear; lia). change (2 ^ 3)%Z with 8%Z.
    ub. do 2 zstep.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bsegs [] m1 m1 Da (Z.of_nat (bn_top ba)) 0 (Z.of_nat k) ad ACDA MU0 Logic.I ALDA BDA eq_refl ltac:(lia) ltac:(lia)
                   ltac:(clear - Hk; lia) ltac:(sh_addr_k)) as RD); zstep; clear RD.
    chk0.
    zstep. ub. do 2 zstep.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bsegs [] m1 m1 Db (Z.of_nat (bn_top ba)) 0 (Z.of_nat k) ad ACDB MU0 Logic.I ALDB BDB eq_refl ltac:(lia) ltac:(lia)
                   ltac:(clear - Hk; lia) ltac:(sh_addr_k)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bsegs m1 Da la k x ad HA Ex ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bsegs m1 Db lb k y ad HB Ey ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD.
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

  Lemma BN_ucmp_specA :
    rw_cells bsegs m A (bn_cells Da ba) -> rw_cells bsegs m B (bn_cells Db bb) ->
    limbs_at bsegs m Da la -> limbs_at bsegs m Db lb ->
    stk bsegs m lo SP -> mem_inv bsegs m ->
    shb_cells bsegs 6163672 6961656 m -> acc bsegs m A 24 -> acc bsegs m B 24 ->
    acc bsegs m Da (8 * Z.of_nat (bn_top ba)) -> acc bsegs m Db (8 * Z.of_nat (bn_top bb)) ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 B ->
    ub_ptr_ok (Z.of_nat (bn_top ba)) Da -> ub_ptr_ok (Z.of_nat (bn_top bb)) Db ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BN_UCMP) fc None m (seg_rom bsegs)).
  Proof.
    intros SA SB RA RB STK MI0 (SHB1 & SHB2) ACA ACB ACDA ACDB EA0 EA1 UDA UDB.
    unfold BN_UCMP. subst a0 a1. unfold SHLO, SHHI in *. pose proof MI0 as MI0'. apply hide_intro in MI0'.
    pose proof (munch_refl [(SP - 80, SP)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (OFF : offshW [(SP - 80, SP)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
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
    assert (PT0 : hide ((0 < Z.of_nat (bn_top ba))%Z -> bn_top bb = bn_top ba -> PTRS)).
    { apply hide_intro. intros HT ET. unfold PTRS.
      destruct (UDA HT) as (PA1 & _). destruct (UDB ltac:(rewrite ET; exact HT)) as (PB1 & _).
      pose proof (limbs_at_47 m Da la RA MI0 ltac:(rewrite LLA; clear - HT; lia)) as BD1. rewrite LLA in BD1.
      pose proof (limbs_at_47 m Db lb RB MI0 ltac:(rewrite LLB, ET; clear - HT; lia)) as BD2. rewrite LLB, ET in BD2.
      clear - PA1 PB1 BD1 BD2. lia. }
    clear UDA UDB.
    unfold wz in SA, SB.
    apply (flag_cell_split bsegs m A _ _ _ _ (bn_flags ba) FRA) in SA.
    apply (flag_cell_split bsegs m B _ _ _ _ (bn_flags bb) FRB) in SB.
    carve_frame 80%nat STK.
    do 11 step.
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K A0; lia|]. clear K.
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K B0; lia|]. clear K.
    ub; do 3 step.
    do 2 step. shl. chk0.
    ub; do 2 step. shl. chk0.
    step. do 3 step. shl. step. chk0.
    step. rewrite (zxb_small (bn_flags ba)) by (clear - FRA; lia). step.
    rewrite (unsigned_lit (bn_flags ba)) by (clear - FRA; lia). rewrite EL4A. step. if_false.
    do 3 step. shl. chk0.
    step. rewrite (zxb_small (bn_flags bb)) by (clear - FRB; lia). step.
    rewrite (unsigned_lit (bn_flags bb)) by (clear - FRB; lia). rewrite EL4B. step. if_false.
    do 3 step. shl. chk0.
    do 3 step. shl. step. chk0.
    step.
    rewrite (sx32_small (Z.of_nat (bn_top ba))) by (clear - TA31; lia).
    rewrite (sx32_small (Z.of_nat (bn_top bb))) by (clear - TB31; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (UI : UINV m1).
    { unfold UINV. split; [|split; [|split; [|split]]].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; rewrite LLA; clear - SEPDA; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LLB; clear - SEPDB; lia].
      - destruct (Nat.eq_dec (bn_top ba) 0) as [E0|N0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia|].
        pose proof (limbs_at_47 m Da la RA (hide_elim _ MI0') ltac:(rewrite LLA; clear - N0; lia)) as BD. rewrite LLA in BD.
        eapply (acc_munch bsegs _ m m1 Da _ ACDA MU OFF); lia.
      - destruct (Nat.eq_dec (bn_top bb) 0) as [E0|N0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia|].
        pose proof (limbs_at_47 m Db lb RB (hide_elim _ MI0') ltac:(rewrite LLB; clear - N0; lia)) as BD. rewrite LLB in BD.
        eapply (acc_munch bsegs _ m m1 Db _ ACDB MU OFF); lia.
      - split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear RA RB FR STK MU WM.
    zstep. ub; zstep.
    replace (Z.of_nat (bn_top ba) + - Z.of_nat (bn_top bb))%Z with (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb))%Z by (clear; lia).
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by (clear; lia).
    change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite (bn_swrap32_mod (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb)) 0) by (clear - TA31 TB31; lia). rewrite Z.add_0_r.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      eapply uc_ret; [exact UI | | clear - TA31 TB31; lia]. unfold ucmp_pure. cbv zeta.
      destruct (Z.eqb_spec (Z.of_nat (bn_top ba) - Z.of_nat (bn_top bb)) 0) as [E0|_]; [contradiction | reflexivity].
    - rewrite land64_zero_iff in K by (clear - TA31 TB31; lia).
      assert (ET : bn_top bb = bn_top ba) by (clear - K; lia).
      zstep. rewrite (bn_swrap32_small (Z.of_nat (bn_top ba) + -1)) by (clear - TA31; lia).
      ub; zstep. rewrite lts_signed by (clear - TA31; lia). if_cases K3; zify_cond K3.
      {
        eapply uc_zero; [exact UI|]. unfold ucmp_pure. cbv zeta. rewrite K. cbn [Z.eqb].
        assert (T0 : bn_top ba = 0%nat) by (clear - K3; lia). rewrite ET, T0. reflexivity. }
      assert (PT : PTRS).
      { apply hide_elim in PT0. apply PT0; [clear - K3; lia | exact ET]. }
      ub.
      replace (Z.land Da 18446744073709551615) with Da
        by (symmetry; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; clear - PT; unfold PTRS in PT; lia).
      replace (Z.land Db 18446744073709551615) with Db
        by (symmetry; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; clear - PT; unfold PTRS in PT; lia).
      replace (0 <? Da)%Z with true by (symmetry; apply Z.ltb_lt; clear - PT; unfold PTRS in PT; lia).
      replace (0 <? Db)%Z with true by (symmetry; apply Z.ltb_lt; clear - PT; unfold PTRS in PT; lia).
      change (Z.b2z true) with 1%Z.
      assert (EK : exists k, bn_top ba = S k) by (clear - K3; destruct (bn_top ba); [exfalso; lia | eexists; reflexivity]).
      destruct EK as (k & EK).
      setreg 12%Z (Z_to_bv 64 (Z.of_nat (S k))) ltac:(rewrite EK; reflexivity).
      eapply uc_loop; [exact UI | exact PT | rewrite EK; clear; lia | exact ET |].
      unfold ucmp_pure. cbv zeta. rewrite K. cbn [Z.eqb].
      rewrite <- EK, ET, !firstn_firstn, Nat.min_id. reflexivity.
  Qed.
End Proofs.
