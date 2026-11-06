(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_tables.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_tables Od_plus Od_nest_plus.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmNest.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Variable pi : Z.
  Hypothesis HPI : (1 <= pi)%Z.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition nest_next (st st' : ost) : Prop :=
    od_next_ok bs idxs 2 st st' \/ od_next_ok bs idxs 2 (consume 2 st) st'.

  Lemma un_elem : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_ok bs idxs 2 st -> (pi < o_pos st)%Z -> frm0 xfc -> NODINV E st m1 ->
    nhead_any E pi Q (nest_next st) ->
    evt usegs Q (NSTu E pi 0x28a78 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST HPI.
    intros Q st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 HH HPP FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (HD3 : o_depth st = 3%Z) by lia.
    od_env OK. od_envu OKU.

    pose proof (acc_plus_ok bs idxs S1 HLAST 2 st st ltac:(lia) HH (acc_none bs idxs 2 st)) as PO0.
    pose proof (acc_plus_ok bs idxs S1 HLAST 2 st (consume 2 st) ltac:(lia) HH (acc_scalar bs idxs 2 st)) as PO1.
    assert (K_NONE : forall yra ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7,
              evt usegs Q (NSTu E pi 0x28b90 yra xt0 xt1 xt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (o_IDX E)) xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros. eapply (un_plus E OK OKU HLAST pi HPI Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 PO0 HPP FRM INV).
      intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' P' F' I'. apply (HK st'); [left; exact P'| exact F'| exact I']. }
    assert (K_CONS : forall yra ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 mm, NODINV E (consume 2 st) mm ->
              evt usegs Q (NSTu E pi 0x28b90 yra xt0 xt1 xt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (o_IDX E)) xt3 xt4 xt5 xt6 xF xfc mm)).
    { intros yra ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 mm INV2.
      eapply (un_plus E OK OKU HLAST pi HPI Q (consume 2 st) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm PO1 ltac:(cbn [consume o_setd o_adv o_pos]; lia) FRM INV2).
      intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' P' F' I'. apply (HK st'); [right; exact P'| exact F'| exact I']. }
    nod_open INV. rewrite HD3 in ITER.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0. pose proof (od_B_range E BOK (off + 1)) as R1.
    pose proof (od_B_range E BOK (off + 2)) as R2. pose proof (od_B_range E BOK (off + 3)) as R3.
    pose proof (od_B_range E BOK (off + 4)) as R4.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    pose proof (tokB_read m1 E (off + 1) BUFRO ltac:(lia)) as RB1.
    pose proof (tokB_read m1 E (off + 2) BUFRO ltac:(lia)) as RB2.
    pose proof (tokB_read m1 E (off + 3) BUFRO ltac:(lia)) as RB3.
    pose proof (tokB_read m1 E (off + 4) BUFRO ltac:(lia)) as RB4.
    set (b0 := B bs off) in *. set (b1 := B bs (off + 1)) in *. set (b2 := B bs (off + 2)) in *.
    set (b3 := B bs (off + 3)) in *. set (b4 := B bs (off + 4)) in *.
    pose proof (usow_read m1 b4 MI ltac:(lia)) as RT4. pose proof (osow_range b4) as RS4. unfold UT_SOW in RT4.
    pose proof (od_al_it E OKU) as A8. pose proof (od_al_tok E OKU (o_pos st)) as A4.

    zstep. zstep. gtrap. zstep. gtrap. zstep. odnorm. zstep. gtrap. zstep. zstep.
    if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.

    zstep. odnorm. zstep. gtrap. zstep. gtrap. zstep. ual. zstep. gtrap. zstep. zstep. odnorm.

    zstep. zstep. gtrap. zstep. zstep. zstep. unz. zstep. gtrap.

    zstep. odnorm. zstep. odnorm. zstep. odnorm. zstep. odnorm.
    zstep. zstep. zstep. zstep. zstep. zstep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let w := fresh "w" in set (w := Z_to_bv 64 (Z.lor x y)) in *; clearbody w end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => let w := fresh "v" in set (w := Z_to_bv 64 (Z.shiftl x y)) in *; clearbody w end.

    zstep. zstep.
    if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply K_NONE]. od_st_eq.
    -
      zstep. zstep. gtrap. zstep. zstep. zstep. odnorm. zstep. zstep. gtrap. zstep. zstep. odnorm. zstep. zstep. gtrap. zstep.
      if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply K_NONE]. od_st_eq.
      +
        zstep. if_cases K3; zify_cond K3; try (exfalso; lia). clear K3.
        zstep. odnorm. zstep. gtrap. zstep. gtrap. zstep. zstep. gtrap. zstep. zstep. ual. zstep. zstep. gtrap.

        od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
        fold off in RD3.
        zstep. odnorm. zstep. zstep. gtrap. zstep. zstep. zstep. unz. zstep. gtrap.
        zstep. zstep. zstep. gtrap. zstep.
        eapply evt_eq; [| eapply K_CONS; nod_close]. od_st_eq.
  Qed.

  Definition nest_pre (st : ost) : Prop :=
    (pi < o_pos st)%Z /\
    (od_head_ok bs idxs 2 st \/
     (o_depth st = 1%Z /\ od_plus_ok bs idxs 1 st) \/
     (o_err st = TAPE_ERROR /\ (2 <= o_depth st <= o_pos st + 4)%Z /\ (o_pos st <= n + 1)%Z /\ o_alive st = true /\ (0 <= o_sbo st)%Z)).

  Lemma nest_pre_next : forall st st', (pi < o_pos st)%Z -> nest_next st st' -> nest_pre st' /\ (o_pos st < o_pos st')%Z.
  Proof using OK HPI.
    intros st st' HP NX. od_env OK.
    assert (G : forall st0, (o_pos st <= o_pos st0)%Z -> od_next_ok bs idxs 2 st0 st' -> nest_pre st' /\ (o_pos st < o_pos st')%Z).
    { intros st0 H0 NX0. pose proof NX0 as (A1 & A2 & A3 & A4 & A5). split; [|lia]. split; [lia|].
      destruct A5 as [(B1 & B2)|[(B1 & B2 & B3)|B]].
      - right; right. destruct A3 as [A3 _]. repeat split; try assumption; lia.
      - right; left. split; [exact B2|]. apply (od_closed_plus_ok bs idxs S1 1 st0 st' ltac:(lia) ltac:(lia) NX0 B1 B2).
      - left. exact B. }
    destruct NX as [NX|NX].
    - apply (G st); [lia| exact NX].
    - apply (G (consume 2 st)); [cbn [consume o_setd o_adv o_pos]; lia| exact NX].
  Qed.

  Lemma un_head : forall (Q : machine_state -> Prop) sti st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    o_pos sti = pi -> od_plus_k E Q sti -> nest_pre st -> frm0 xfc -> NODINV E st m1 ->
    (od_head_ok bs idxs 2 st -> nhead_any E pi Q (nest_next st)) ->
    evt usegs Q (NSTu E pi ON_HEAD xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST HPI.
    intros Q sti st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 HSTI HKP [HPOS PRE] FRM INV HEL. unfold ON_HEAD.
    od_env OK. od_envu OKU.
    assert (DR : (0 <= o_depth st <= o_pos st + 4 /\ o_pos st <= n + 1 /\ (o_err st = 0 \/ o_err st = 3))%Z)
      by (destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & (HP & HPD & HD & HE & HA & HB))|(HE & HD & HP & HA & HB)]]; unfold TAPE_ERROR in *; lia).
    pose proof HKP as HKP0. unfold od_plus_k, OD_PLUS in HKP0.
    assert (INV2 := INV). pose proof INV as [INVO _]. nod_open INV.

    zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    zstep. odnorm. zstep.
    if_cases KD; zify_cond KD; odsig KD.
    -
      destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & PO)|(HE & HD & HP & HA & HB)]]; try (exfalso; lia).
      eapply evt_eq; [| eapply (HKP0 st); [split; [lia| left; exact PO]| exact FRM| exact INVO]]. od_st_eq.
    -
      zstep. zstep. zstep. if_false.
      zstep. odnorm. zstep. zstep. gtrap. zstep.
      if_cases KE; zify_cond KE.
      +
        destruct PRE as [HH|[(HD1 & PO)|(HE & HD & HP & HA & HB)]]; [| exfalso; lia| exfalso; unfold TAPE_ERROR in HE; lia].
        eapply evt_eq; [| eapply (un_elem Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HH HPOS FRM INV2 (HEL HH))]. od_st_eq.
      +
        destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & (HP & HPD & HD & HE & HA & HB))|(HE & HD & HP & HA & HB)]]; try (exfalso; lia).
        pose proof HE as HE3. unfold TAPE_ERROR in HE3.
        lstep. lstep. zstep.

        zstep. odnorm. zstep. zstep. gtrap. zstep. zstep.
        if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.

        zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
        zstep. odnorm. zstep. if_true.
        eapply evt_eq; [| eapply (HKP0 (o_abandon st)); [split; [cbn [o_abandon o_pos]; lia| right; unfold od_dead; cbn [o_abandon o_alive o_depth o_err o_sbo]; repeat split; assumption]| exact FRM|]].
        * od_st_eq.
        * match goal with HH : rw_cells _ _ (bv_unsigned (o_sp _) + -328)%Z [C8 _] |- _ => od_forget HH end. od_close_inv.
  Qed.

  Lemma un_loop : forall (Q : machine_state -> Prop) sti, o_pos sti = pi -> od_plus_k E Q sti ->
    forall (fuel : nat) st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    (o_left idxs st <= Z.of_nat fuel)%Z -> nest_pre st -> frm0 xfc -> NODINV E st m1 ->
    evt usegs Q (NSTu E pi ON_HEAD xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_IDX E)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST HPI.
    intros Q sti HSTI HKP fuel.
    induction fuel as [|f IH]; intros st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 HF PRE FRM INV.
    all: apply (un_head Q sti st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HSTI HKP PRE FRM INV).
    all: intros HH; pose proof HH as (HP & _); unfold o_left in HF.
    - exfalso. lia.
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' NX F' I'.
      destruct PRE as [HPOS _].
      destruct (nest_pre_next st st' HPOS NX) as [PRE' LT].
      apply (IH st'); [unfold o_left; lia| exact PRE'| exact F'| exact I'].
  Qed.
End ArmNest.

Section Arm.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Theorem od_arm_nest : arm_stmt E 0x2793c.
  Proof using OK OKU.
    unfold arm_stmt. intros Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (HD2 : o_depth st = 2%Z) by lia.
    assert (HPI : (1 <= o_pos st)%Z) by lia.
    assert (INV2 := INV). od_open_inv INV. od_env OK. od_envu OKU. rewrite HD2 in ITER.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_tokI_range E S1 (o_pos st + 1) ltac:(lia)) as TR1.
    pose proof (od_tokT_range E BOK (o_pos st + 1)) as CR1.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    pose proof (tokB_read m1 E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2.
    fold (tokT bs idxs (o_pos st)) in RD2.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.
    set (c1 := tokT bs idxs (o_pos st + 1)) in *.
    pose proof (od_al_it E OKU) as A8. pose proof (od_al_tok E OKU (o_pos st)) as A4.
    assert (A4b : ((o_IDX E + 4 * o_pos st + 4) mod 4 = 0)%Z).
    { replace (o_IDX E + 4 * o_pos st + 4)%Z with (o_IDX E + 4 * (o_pos st + 1))%Z by lia. apply (od_al_tok E OKU). }

    zstep. if_false.
    zstep. gok. zstep. ual. zstep. gok.
    zstep. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.

    zstep. odnorm. zstep. gok. zstep. gok. zstep. gok. zstep. ual. zstep. gok.

    zstep. zstep. odnorm. zstep. zstep. gok. zstep. zstep. zstep. unz. zstep. gok. zstep. gok.
    zstep. odnorm. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. lstep.

      zstep. if_true. zstep. zstep. zstep. if_true.
      zstep. if_true. zstep. zstep. zstep. if_false. zstep.
      od_forget FR168.
      eapply evt_eq; [| eapply (HK0 st); [| exact FRM| od_close_inv]]; [od_st_eq|].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      zstep. gok. zstep. zstep. gok. zstep. zstep.
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RD3).
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) BUFRO ltac:(lia)) as RD4).
      fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
      replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
      set (off1 := tokI bs idxs (o_pos st + 1)) in *.

      zstep. gok. zstep. zstep. gok. zstep. zstep. gok. zstep. odnorm. zstep. gok. zstep. gok. zstep. ual. zstep. gok.

      zstep. odnorm. zstep. zstep. gok. zstep. zstep. odnorm. zstep. zstep.
      assert (SA : start_array bs idxs 1 st = if (c1 =? 93)%Z then (o_setd (o_adv st 2) 1, true) else (o_setd (o_adv st 1) 3, true)).
      { unfold start_array. fold c. fold c1. unfold C_LBRACKET, C_RBRACKET. rewrite (proj2 (Z.eqb_eq c 91)) by lia. reflexivity. }
      if_cases K2; zify_cond K2.
      +
        zstep. zstep. gtrap. zstep. zstep. zstep. gtrap. zstep. zstep. gtrap. zstep. zstep.
        zstep. zstep. lstep.
        eapply evt_eq; [| eapply (un_loop E OK OKU HLAST (o_pos st) HPI Q st eq_refl HK (Z.to_nat (n + 1)) (o_setd (o_adv st 1) 3)); [| | exact FRM| nod_close]].
        * unfold ON_HEAD. od_st_eq.
        * unfold o_left. cbn [o_setd o_adv o_pos]. lia.
        * split; [cbn [o_setd o_adv o_pos]; lia|]. left.
          apply (od_inner_head_ok bs idxs S1 HLAST 1 st ltac:(lia) HH); [unfold C_LBRACKET; fold c; lia| unfold C_RBRACKET; fold c1; lia].
      +
        zstep. gok. zstep. gok. zstep. zstep. gok. zstep. zstep. zstep. zstep. gok. zstep. zstep.
        zstep. zstep. zstep. zstep. lstep.
        eapply evt_eq; [| eapply (un_loop E OK OKU HLAST (o_pos st) HPI Q st eq_refl HK (Z.to_nat (n + 1)) (o_setd (o_adv st 2) 1)); [| | exact FRM| nod_close]].
        * unfold ON_HEAD. od_st_eq.
        * unfold o_left. cbn [o_setd o_adv o_pos]. lia.
        * split; [cbn [o_setd o_adv o_pos]; lia|]. right; left. split; [reflexivity|].
          pose proof (acc_plus_ok bs idxs S1 HLAST 1 st _ ltac:(lia) HH (acc_array bs idxs 1 st)) as PO.
          rewrite SA in PO. rewrite (proj2 (Z.eqb_eq c1 93)) in PO by lia. exact PO.
  Qed.
End Arm.
