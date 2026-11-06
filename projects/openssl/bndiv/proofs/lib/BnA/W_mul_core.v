(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnModel BnMInv.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnKaraMem W_mul_normal BnCalls W_mul_recursive W_mul_part_recursive.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnArr BnRep.
From OSSVerify.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Section Core.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo R A B Dr Da Db CST : Z) (br : bignum bptr) (la lb : list Z).
  Notation SP := (bv_unsigned sp).
  Notation al := (Z.of_nat (length la)).
  Notation bl := (Z.of_nat (length lb)).
  Notation dmx := (Z.of_nat (bn_dmax br)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -112)).

  (* [comment removed for export] *)
  Definition mulc_pre : Prop :=
    limbs la /\ limbs lb /\ bn_okm br /\ (al < 8388608 /\ bl < 8388608)%Z /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * al <= lo /\ 0 <= Db /\ Db + 8 * bl <= lo /\
     0 <= CST /\ lo <= SP - 112 - CST /\ SP < 2^64)%Z /\
    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * al <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * bl <= R)%Z /\
    (Dr + 8 * dmx <= Da \/ Da + 8 * al <= Dr)%Z /\ (Dr + 8 * dmx <= Db \/ Db + 8 * bl <= Dr)%Z.
  Hypothesis PRE : mulc_pre.

  Lemma P_lists : limbs la /\ limbs lb /\ bn_okm br /\ (al < 8388608 /\ bl < 8388608)%Z.
  Proof. destruct PRE as (H1 & H2 & H3 & H4 & _). auto. Qed.
  Lemma P_rng : (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * al <= lo /\ 0 <= Db /\ Db + 8 * bl <= lo /\
     0 <= CST /\ lo <= SP - 112 - CST /\ SP < 18446744073709551616)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_sarr : (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * al <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * bl <= R)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & H1 & H2 & H3 & _). auto. Qed.
  Lemma P_disj : (Dr + 8 * dmx <= Da \/ Da + 8 * al <= Dr)%Z /\ (Dr + 8 * dmx <= Db \/ Db + 8 * bl <= Dr)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2). auto. Qed.

  (* [comment removed for export] *)
  Definition mulc_mem : Prop :=
    rw_cells psegs m R (bn_cells Dr br) /\ u64arr psegs m Dr (wlimbs (bn_buf br)) /\
    rw_cells psegs m A [C8 (wz Da)] /\ rw_cells psegs m B [C8 (wz Db)] /\
    limbs_at psegs m Da la /\ limbs_at psegs m Db lb /\
    stk psegs m lo (SP + -112) /\ mem_inv psegs m.
  Hypothesis MEM : mulc_mem.

  (* [comment removed for export] *)
  Definition mulc_post (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (W : list (Z * Z)) (topn : nat) (w : list Z)
      (Q : (word -> option byte) -> Prop) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F (Z_to_bv 64 0x10a7ec) fc None m' (seg_rom psegs)
      /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rw_cells psegs m' R [C8 (wz Dr); C4 (wz (Z.of_nat topn)); C4 (wz dmx); C4 (wz (Z.b2z (bn_neg br))); C4 (wz (bn_flags br))]
      /\ limbs_at psegs m' Dr w /\ stk psegs m' lo (SP + -112) /\ Q m'.

  (* [comment removed for export] *)
  Lemma mulc_normal : forall x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x25 x26 x27 t3 t4 t5 t6,
    (length la + length lb <= bn_dmax br)%nat -> (144 <= CST)%Z ->
    evt psegs (mulc_post x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 (al + bl)) x25 x26 x27
                 [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z (length la + length lb) (mul_normal la lb) (fun _ => True))
      (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 R) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R)
               (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 (al + bl)) x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10a77c) fc None m (seg_rom psegs)).
  Proof.
    intros x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x25 x26 x27 t3 t4 t5 t6 HD HCST.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB).
    pose proof (munch_refl [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    assert (HW : wr_at psegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at psegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K RNG; lia|]. clear K.
    do 3 zstep. zstep. do 2 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    assert (HLA0 : limbs_at psegs m0 Da la) by (eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]).
    assert (HLB0 : limbs_at psegs m0 Db lb) by (eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]).
    clear HLA HLB MUt.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    eapply (call_mul_normal (mulc_post x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 (al + bl)) x25 x26 x27
                 [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z (length la + length lb) (mul_normal la lb) (fun _ => True)))
      with (a := la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -112)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI
      | exact LLA | exact LLB | clear - AL23 BL23; lia
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - AL23; lia
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - BL23; lia
      | exact HLA0 | exact HLB0
      | replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | clear - DA HD; unfold bn_dmax in *; lia | clear - DB HD; unfold bn_dmax in *; lia
      | clear - RNG HCST; lia | clear - RNG HD HCST; unfold bn_dmax in *; lia | clear - RNG HCST; lia | clear - RNG HCST; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.
    zstep. apply evt_done.
    unfold mulc_post. do 16 eexists. exists m2. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCST. lia. }
    split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
    split. { eapply rw_cells_transport; [| exact MUc | exact WMc | cbn; clear - SA1 RNG HD HCST; unfold bn_dmax in *; lia].
             unfold wz. rewrite Nat2Z.inj_add. exact SR. }
    split; [exact HRc|]. split; [exact STc | exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma mulc_comba8 : forall CS8 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x23 x24 x25 x26 x27 t3 t4 t5 t6,
    comba8_spec CS8 -> (CS8 <= CST)%Z -> length la = 8%nat -> length lb = 8%nat -> (16 <= bn_dmax br)%nat ->
    evt psegs (mulc_post x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 16) x23 x24 x25 x26 x27
                 [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z 16 (mul_comba8 la lb) (fun _ => True))
      (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 R) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R)
               (Z_to_bv 64 16) x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10a6a0) fc None m (seg_rom psegs)).
  Proof.
    intros CS8 x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x23 x24 x25 x26 x27 t3 t4 t5 t6 C8 HCS LA8 LB8 HD.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI).
    pose proof P_lists as (LLA & LLB & OKR & _). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB).
    pose proof (munch_refl [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    assert (HW : wr_at psegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at psegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    zstep. if_cases K; zify_cond K; [exfalso; clear - K RNG; lia|]. clear K.
    do 3 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    assert (HLA0 : limbs_at psegs m0 Da la) by (eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]).
    assert (HLB0 : limbs_at psegs m0 Db lb) by (eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]).
    clear HLA HLB MUt.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    eapply (call_comba8 (mulc_post x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 16) x23 x24 x25 x26 x27
                 [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z 16 (mul_comba8 la lb) (fun _ => True)))
      with (CS8 := CS8) (a := la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -112)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact C8
      | exact LLA | exact LLB | exact LA8 | exact LB8
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | exact HLA0 | exact HLB0
      | replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | clear - DA HD LA8; unfold bn_dmax in *; lia | clear - DB HD LB8; unfold bn_dmax in *; lia
      | clear - RNG HCS; lia | clear - RNG HD HCS; unfold bn_dmax in *; lia | clear - RNG HCS LA8; lia | clear - RNG HCS LB8; lia | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.
    zstep. apply evt_done.
    unfold mulc_post. do 16 eexists. exists m2. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCS. lia. }
    split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
    split. { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 RNG HD HCS; unfold bn_dmax in *; lia]. }
    split; [exact HRc|]. split; [exact STc | exact I].
  Qed.

  (* [comment removed for export] *)
  Definition mulc_tpre (TT Dt : Z) (Tl : list Z) : Prop :=
    limbs Tl /\ rw_cells psegs m TT [C8 (wz Dt)] /\ limbs_at psegs m Dt Tl /\ wr_at psegs m Dt (8 * Z.of_nat (length Tl)) /\
    (0 <= Dt /\ Dt + 8 * Z.of_nat (length Tl) <= lo)%Z /\
    (R + 24 <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= R)%Z /\
    (Dt + 8 * Z.of_nat (length Tl) <= Da \/ Da + 8 * al <= Dt)%Z /\ (Dt + 8 * Z.of_nat (length Tl) <= Db \/ Db + 8 * bl <= Dt)%Z /\
    (Dr + 8 * dmx <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= Dr)%Z.

  (* [comment removed for export] *)
  Lemma mulc_rec : forall CS8 (k da db : nat) TT Dt Tl x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6,
    rec_spec_at CS8 k -> (rec_stack CS8 k <= CST)%Z -> mulc_tpre TT Dt Tl ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat -> length la = (Nat.pow 2 k - da)%nat -> length lb = (Nat.pow 2 k - db)%nat ->
    (2 * Nat.pow 2 k <= bn_dmax br)%nat -> (scratch_rec k <= length Tl)%nat ->
    evt psegs (mulc_post x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 (al + bl))
                 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) x27
                 [(Dr, Dr + 8 * Z.of_nat (2 * Nat.pow 2 k)); (Dt, Dt + 8 * Z.of_nat (length Tl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z
                 (length la + length lb)
                 (fst (mul_recursive k la lb da db (firstn (2 * Nat.pow 2 k) (bn_buf br)) Tl))
                 (fun m' => limbs_at psegs m' Dt (snd (mul_recursive k la lb da db (firstn (2 * Nat.pow 2 k) (bn_buf br)) Tl))))
      (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 R) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R)
               (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10a748) fc None m (seg_rom psegs)).
  Proof.
    intros CS8 k da db TT Dt Tl x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6 RSPEC HCS TPRE HK HDA HDB LA LB HD HSC.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI).
    destruct TPRE as (LLT & HTd & HLT & HWT & RT & ST1 & DTA & DTB & DTR).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB).
    pose proof OKR as (LBR & _).
    set (Rl := firstn (2 * Nat.pow 2 k) (bn_buf br)).
    assert (LRl : length Rl = (2 * Nat.pow 2 k)%nat) by (subst Rl; apply firstn_length_le; unfold bn_dmax in HD; exact HD).
    pose proof (munch_refl [(Dr, Dr + 8 * Z.of_nat (2 * Nat.pow 2 k)); (Dt, Dt + 8 * Z.of_nat (length Tl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    assert (HLR : limbs_at psegs m Dr Rl) by (subst Rl; apply (limbs_at_firstn psegs); apply limbs_at_of_u64arr; exact UR).
    assert (HW : wr_at psegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at psegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    assert (P2 : (0 < Z.of_nat (Nat.pow 2 k))%Z) by (pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia).
    zstep. if_cases K; zify_cond K; [exfalso; clear - K RNG; lia|]. clear K.
    do 4 zstep.
    zstep. rewrite (bn_swrap32_small (al - Z.of_nat (Nat.pow 2 k))) by (clear - AL23 LA HDA P2; lia).
    zstep. rewrite (bn_swrap32_small (bl - Z.of_nat (Nat.pow 2 k))) by (clear - BL23 LB HDB P2; lia).
    zstep.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    lazymatch goal with |- evt _ ?P _ =>
      eapply (call_rec P) with (CS8 := CS8) (k := k) (a := la) (b := lb) (da := da) (db := db) (R := Rl) (T := Tl)
        (RP := Dr) (AP := Da) (BP := Db) (TQ := Dt) (lo := lo) (SPz := (SP + -112)%Z) end;
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact RSPEC
      | exact LLA | exact LLB | subst Rl; apply limbs_firstn; exact LBR | exact LLT
      | exact HK | exact HDA | exact HDB | exact LA | exact LB | exact LRl | exact HSC
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | apply unsigned_lit; clear - P2 AL23 LA HDA; lia
      | f_equal; clear - LA P2 HDA; lia | f_equal; clear - LB P2 HDB; lia
      | apply unsigned_lit; clear - RT RNG; lia
      | exact HLA | exact HLB | exact HLR | exact HLT
      | rewrite LRl; replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | exact HWT
      | rewrite LRl; clear - DA HD; unfold bn_dmax in *; lia | rewrite LRl; clear - DB HD; unfold bn_dmax in *; lia
      | clear - DTA; lia | clear - DTB; lia
      | rewrite LRl; clear - DTR HD; unfold bn_dmax in *; lia
      | clear - RNG HCS; lia | rewrite LRl; clear - RNG HD HCS; unfold bn_dmax in *; lia | clear - RNG RT HCS; lia
      | clear - RNG HCS; lia | clear - RNG HCS; lia | ].
    rewrite LRl. intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc HTc STc.
    pose proof (mul_recursive_spec k la lb da db Rl Tl LLA LLB ltac:(subst Rl; apply limbs_firstn; exact LBR) LLT ltac:(lia) HDA HDB LA LB LRl HSC) as MP.
    destruct (mul_recursive k la lb da db Rl Tl) as [ro to]. cbn [fst snd] in *. destruct MP as (_ & NRO & _ & _ & NTO).
    assert (SR2 : rw_cells psegs m2 R [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top br))); C4 (wz dmx); C4 (wz (Z.b2z (bn_neg br))); C4 (wz (bn_flags br))]).
    { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 ST1 RNG HD HCS; unfold bn_dmax in *; lia]. }
    assert (MU2 : munch [(Dr, Dr + 8 * Z.of_nat (2 * Nat.pow 2 k)); (Dt, Dt + 8 * Z.of_nat (length Tl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCS. lia. }
    pose proof (wmono_trans _ _ _ _ WM WMc) as WM2.
    clear SR HAd HBd HLA HLB HLR HLT HW HWT ST MI MU WM MUc WMc.
    pose proof (munch_refl [(R, R + 24)]%Z m2) as MUt.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    apply evt_done.
    unfold mulc_post. do 16 eexists. exists m3. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MIc|].
    split. { unfold wz. rewrite Nat2Z.inj_add. exact SR2. }
    split. { eapply limbs_at_transport; [exact HRc | exact MUt |]. cbn [disjoint_from]. rewrite NRO, LRl. clear - SA1 HD. unfold bn_dmax in *. lia. }
    split; [exact STc|].
    eapply limbs_at_transport; [exact HTc | exact MUt |]. cbn [disjoint_from]. rewrite NTO. clear - ST1. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma mulc_part : forall CS8 (fuel k tna tnb : nat) TT Dt Tl x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6,
    part_spec_at CS8 fuel -> (part_stack CS8 k <= CST)%Z -> mulc_tpre TT Dt Tl ->
    (3 <= k)%nat -> (k <= fuel)%nat -> (k <= 26)%nat ->
    (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
    length la = (Nat.pow 2 k + tna)%nat -> length lb = (Nat.pow 2 k + tnb)%nat ->
    (4 * Nat.pow 2 k <= bn_dmax br)%nat -> (8 * Nat.pow 2 k <= length Tl)%nat ->
    evt psegs (mulc_post x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 (al + bl))
                 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) x27
                 [(Dr, Dr + 8 * Z.of_nat (4 * Nat.pow 2 k)); (Dt, Dt + 8 * Z.of_nat (length Tl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z
                 (length la + length lb)
                 (fst (mul_part_recursive fuel k la lb tna tnb (firstn (4 * Nat.pow 2 k) (bn_buf br)) Tl))
                 (fun m' => limbs_at psegs m' Dt (snd (mul_part_recursive fuel k la lb tna tnb (firstn (4 * Nat.pow 2 k) (bn_buf br)) Tl))))
      (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 R) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R)
               (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10a7c4) fc None m (seg_rom psegs)).
  Proof.
    intros CS8 fuel k tna tnb TT Dt Tl x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6 RSPEC HCS TPRE HK3 HKF HK26 HTA HTB HD1 HD2 LA LB HD HSC.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI).
    destruct TPRE as (LLT & HTd & HLT & HWT & RT & ST1 & DTA & DTB & DTR).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB).
    pose proof OKR as (LBR & _).
    set (Rl := firstn (4 * Nat.pow 2 k) (bn_buf br)).
    assert (LRl : length Rl = (4 * Nat.pow 2 k)%nat) by (subst Rl; apply firstn_length_le; unfold bn_dmax in HD; exact HD).
    pose proof (munch_refl [(Dr, Dr + 8 * Z.of_nat (4 * Nat.pow 2 k)); (Dt, Dt + 8 * Z.of_nat (length Tl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    assert (HLR : limbs_at psegs m Dr Rl) by (subst Rl; apply (limbs_at_firstn psegs); apply limbs_at_of_u64arr; exact UR).
    assert (HW : wr_at psegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at psegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    assert (P2 : (0 < Z.of_nat (Nat.pow 2 k))%Z) by (pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia).
    zstep. if_cases K; zify_cond K; [exfalso; clear - K RNG; lia|]. clear K.
    do 4 zstep.
    zstep. rewrite (bn_swrap32_small (al - Z.of_nat (Nat.pow 2 k))) by (clear - AL23 LA P2; lia).
    zstep. rewrite (bn_swrap32_small (bl - Z.of_nat (Nat.pow 2 k))) by (clear - BL23 LB P2; lia).
    zstep.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    lazymatch goal with |- evt _ ?P _ =>
      eapply (call_part P) with (CS8 := CS8) (fuel := fuel) (k := k) (a := la) (b := lb) (tna := tna) (tnb := tnb) (R := Rl) (T := Tl)
        (RP := Dr) (AP := Da) (BP := Db) (TQ := Dt) (lo := lo) (SPz := (SP + -112)%Z) end;
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact RSPEC
      | exact LLA | exact LLB | subst Rl; apply limbs_firstn; exact LBR | exact LLT
      | exact HK3 | exact HKF | exact HK26 | exact HTA | exact HTB | exact HD1 | exact HD2 | exact LA | exact LB | exact LRl | exact HSC
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | apply unsigned_lit; clear - P2 AL23 LA; lia
      | rewrite unsigned_lit by (clear - LA AL23; lia); clear - LA; lia | rewrite unsigned_lit by (clear - LB BL23; lia); clear - LB; lia
      | apply unsigned_lit; clear - RT RNG; lia
      | exact HLA | exact HLB | exact HLR | exact HLT
      | rewrite LRl; replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | exact HWT
      | rewrite LRl; clear - DA HD; unfold bn_dmax in *; lia | rewrite LRl; clear - DB HD; unfold bn_dmax in *; lia
      | clear - DTA; lia | clear - DTB; lia
      | rewrite LRl; clear - DTR HD; unfold bn_dmax in *; lia
      | clear - RNG HCS; lia | rewrite LRl; clear - RNG HD HCS; unfold bn_dmax in *; lia | clear - RNG RT HCS; lia
      | clear - RNG HCS; lia | clear - RNG HCS; lia | ].
    rewrite LRl. intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc HTc STc.
    pose proof (mul_part_recursive_spec fuel k la lb tna tnb Rl Tl LLA LLB ltac:(subst Rl; apply limbs_firstn; exact LBR) LLT HK3 HKF HTA HTB HD1 HD2 LA LB LRl HSC) as MP.
    destruct (mul_part_recursive fuel k la lb tna tnb Rl Tl) as [ro to]. cbn [fst snd] in *. destruct MP as (_ & NRO & _ & _ & NTO).
    assert (SR2 : rw_cells psegs m2 R [C8 (wz Dr); C4 (wz (Z.of_nat (bn_top br))); C4 (wz dmx); C4 (wz (Z.b2z (bn_neg br))); C4 (wz (bn_flags br))]).
    { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 ST1 RNG HD HCS; unfold bn_dmax in *; lia]. }
    assert (MU2 : munch [(Dr, Dr + 8 * Z.of_nat (4 * Nat.pow 2 k)); (Dt, Dt + 8 * Z.of_nat (length Tl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCS. lia. }
    pose proof (wmono_trans _ _ _ _ WM WMc) as WM2.
    clear SR HAd HBd HLA HLB HLR HLT HW HWT ST MI MU WM MUc WMc.
    pose proof (munch_refl [(R, R + 24)]%Z m2) as MUt.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    apply evt_done.
    unfold mulc_post. do 16 eexists. exists m3. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MIc|].
    split. { unfold wz. rewrite Nat2Z.inj_add. exact SR2. }
    split. { eapply limbs_at_transport; [exact HRc | exact MUt |]. cbn [disjoint_from]. rewrite NRO, LRl. clear - SA1 HD. unfold bn_dmax in *. lia. }
    split; [exact STc|].
    eapply limbs_at_transport; [exact HTc | exact MUt |]. cbn [disjoint_from]. rewrite NTO. clear - ST1. lia.
  Qed.
End Core.
