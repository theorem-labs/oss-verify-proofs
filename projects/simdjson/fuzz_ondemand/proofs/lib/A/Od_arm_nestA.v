(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_headA Od_nest_plusA Od_nest_elemA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section ArmNest.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Variable pi : Z.
  Hypothesis HPI : (1 <= pi)%Z.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition nest_pre (st : ost) : Prop :=
    (pi < o_pos st)%Z /\
    (od_head_ok bs idxs 2 st \/
     (o_depth st = 1%Z /\ od_plus_ok bs idxs 1 st) \/
     (o_err st = TAPE_ERROR /\ (2 <= o_depth st <= o_pos st + 4)%Z /\ (o_pos st <= n + 1)%Z /\ o_alive st = true /\ (0 <= o_sbo st)%Z)).

  Lemma nest_pre_next : forall st st', (pi < o_pos st)%Z -> nest_next E st st' -> nest_pre st' /\ (o_pos st < o_pos st')%Z.
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

  Lemma an_head : forall (Q : machine_state -> Prop) sti st xt1 xt2 xa5 xa6 xa7 xs9 xt3 xt4 xF xfc m1,
    o_pos sti = pi -> od_plus_k E Q sti -> nest_pre st -> frm0 xfc -> NODINV E st m1 ->
    (od_head_ok bs idxs 2 st -> nhead_any E Q (nest_next E st)) ->
    evt asegs Q (NSTa E ON_HEAD xt1 xt2 (Z_to_bv 64 1) xa5 xa6 xa7 (Z_to_bv 64 2) xs9 xt3 xt4 (Z_to_bv 64 1) (Z_to_bv 64 1) xF xfc m1).
  Proof using OK HLAST HPI.
    intros Q sti st xt1 xt2 xa5 xa6 xa7 xs9 xt3 xt4 xF xfc m1 HSTI HKP [HPOS PRE] FRM INV HEL. unfold ON_HEAD.
    od_env OK.
    assert (DR : (0 <= o_depth st <= o_pos st + 4 /\ o_pos st <= n + 1 /\ (o_err st = 0 \/ o_err st = 3))%Z)
      by (destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & (HP & HPD & HD & HE & HA & HB))|(HE & HD & HP & HA & HB)]]; unfold TAPE_ERROR in *; lia).
    destruct DR as (DR1 & DR2 & DR3).
    pose proof HKP as HKP0. unfold od_plus_k, OD_PLUS in HKP0.
    assert (INV2 := INV). pose proof INV as [INVO _]. nod_open INV.

    zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    ochkn. ostep. odnorm. ostep.
    if_cases KD; zify_cond KD; odsig KD.
    -
      destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & PO)|(HE & HD & HP & HA & HB)]]; [exfalso; lia| | exfalso; lia].
      eapply evt_eq; [| eapply (HKP0 st); [split; [lia| left; exact PO]| exact FRM| exact INVO]]. od_st_eq.
    -
      ostep. ostep. zstep. if_false.
      ochkn. ostep. odnorm. ostep.
      if_cases KE; zify_cond KE.
      +
        destruct PRE as [HH|[(HD1 & PO)|(HE & HD & HP & HA & HB)]]; [| exfalso; lia| exfalso; unfold TAPE_ERROR in HE; lia].
        eapply evt_eq; [| eapply (an_elem E OK HLAST Q st _ _ _ _ _ _ _ _ _ _ _ m1 HH FRM INV2 (HEL HH))]. od_st_eq.
      +
        destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & (HP & HPD & HD & HE & HA & HB))|(HE & HD & HP & HA & HB)]]; [exfalso; lia| exfalso; lia|].
        pose proof HE as HE3. unfold TAPE_ERROR in HE3.
        ochk. lstep. ostep. ostep. if_false. lstep. ostep. ostep.

        zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
        ochkn. ostep. odnorm. ostep. if_true.
        eapply evt_eq; [| eapply (HKP0 (o_abandon st)); [split; [cbn [o_abandon o_pos]; lia| right; unfold od_dead; cbn [o_abandon o_alive o_depth o_err o_sbo]; repeat split; assumption]| exact FRM|]].
        * od_st_eq.
        * match goal with HH : rw_cells _ _ (oa_S1 _ + 176)%Z [C8 _] |- _ => oa_forget HH end. od_close_inv.
  Qed.

  Lemma an_loop : forall (Q : machine_state -> Prop) sti, o_pos sti = pi -> od_plus_k E Q sti ->
    forall (fuel : nat) st xt1 xt2 xa5 xa6 xa7 xs9 xt3 xt4 xF xfc m1,
    (o_left idxs st <= Z.of_nat fuel)%Z -> nest_pre st -> frm0 xfc -> NODINV E st m1 ->
    evt asegs Q (NSTa E ON_HEAD xt1 xt2 (Z_to_bv 64 1) xa5 xa6 xa7 (Z_to_bv 64 2) xs9 xt3 xt4 (Z_to_bv 64 1) (Z_to_bv 64 1) xF xfc m1).
  Proof using OK HLAST HPI.
    intros Q sti HSTI HKP fuel.
    induction fuel as [|f IH]; intros st xt1 xt2 xa5 xa6 xa7 xs9 xt3 xt4 xF xfc m1 HF PRE FRM INV.
    all: apply (an_head Q sti st _ _ _ _ _ _ _ _ _ _ m1 HSTI HKP PRE FRM INV).
    all: intros HH; pose proof HH as (HP & _); unfold o_left in HF.
    - exfalso. lia.
    - intros st' ? ? ? ? ? ? ? ? ? ? m' NX F' I'.
      destruct PRE as [HPOS _].
      destruct (nest_pre_next st st' HPOS NX) as [PRE' LT].
      apply (IH st'); [unfold o_left; lia| exact PRE'| exact F'| exact I'].
  Qed.
End ArmNest.

Section Arm.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Theorem od_arm_nest : arm_stmt E 0x97474.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (HD2 : o_depth st = 2%Z) by lia.
    assert (HPI : (1 <= o_pos st)%Z) by lia.
    assert (INV2 := INV). od_open_inv INV. od_env OK. rewrite HD2 in ITER.
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

    zstep. if_false.
    ostep. ochk. ostep. ostep. zstep. if_true.

    ostep. ochk. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true.

    ostep. odnorm. ostep. ochk. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. lstep.

      zstep. if_true. ostep. ostep. zstep. if_true.
      zstep. if_true. ostep. ostep. zstep. if_false. ostep.
      oa_forget FR176.
      eapply evt_eq; [| eapply (HK0 st); [| exact FRM| od_close_inv]]; [od_st_eq|].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      ostep. ostep. if_true. ostep. ostep.
      clear RD1 RD2.
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) BUFRO ltac:(lia)) as RD4).
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RD3).
      fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
      replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
      set (off1 := tokI bs idxs (o_pos st + 1)) in *.

      ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. if_true.

      ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. odnorm. ostep. ochk. ostep. odnorm. ostep. zstep.
      assert (SA : start_array bs idxs 1 st = if (c1 =? 93)%Z then (o_setd (o_adv st 2) 1, true) else (o_setd (o_adv st 1) 3, true)).
      { unfold start_array. fold c. fold c1. unfold C_LBRACKET, C_RBRACKET. rewrite (proj2 (Z.eqb_eq c 91)) by lia. reflexivity. }
      if_cases K2; zify_cond K2.
      +
        ostep. ostep. ostep. if_true. ostep. ostep. ostep.
        ostep. ostep. ostep. ostep. ostep. ostep. lstep.
        eapply evt_eq; [| eapply (an_loop E OK HLAST (o_pos st) HPI Q st eq_refl HK (Z.to_nat (n + 1)) (o_setd (o_adv st 1) 3)); [| | exact FRM| nod_close]].
        * unfold ON_HEAD. od_st_eq.
        * unfold o_left. cbn [o_setd o_adv o_pos]. lia.
        * split; [cbn [o_setd o_adv o_pos]; lia|]. left.
          apply (od_inner_head_ok bs idxs S1 HLAST 1 st ltac:(lia) HH); [unfold C_LBRACKET; fold c; lia| unfold C_RBRACKET; fold c1; lia].
      +
        ostep. ostep. if_true. ostep. ostep. ostep. ostep.
        ostep. ostep. if_true. ostep. ostep. ostep.
        ostep. ostep. ostep. ostep. ostep. ostep. lstep.
        eapply evt_eq; [| eapply (an_loop E OK HLAST (o_pos st) HPI Q st eq_refl HK (Z.to_nat (n + 1)) (o_setd (o_adv st 2) 1)); [| | exact FRM| nod_close]].
        * unfold ON_HEAD. od_st_eq.
        * unfold o_left. cbn [o_setd o_adv o_pos]. lia.
        * split; [cbn [o_setd o_adv o_pos]; lia|]. right; left. split; [reflexivity|].
          pose proof (acc_plus_ok bs idxs S1 HLAST 1 st _ ltac:(lia) HH (acc_array bs idxs 1 st)) as PO.
          rewrite SA in PO. rewrite (proj2 (Z.eqb_eq c1 93)) in PO by lia. exact PO.
  Qed.
End Arm.
