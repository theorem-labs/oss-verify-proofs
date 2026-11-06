(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_nest_plusB Od_nest_firstB Od_nest_elemB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Ltac sstep := step; od_fix_lit_store; zsimp; anorm.

Section NestHead.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Variable pi : Z.
  Hypothesis HPI : (1 <= pi)%Z.
  Hypothesis HG : od_shb E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).
  Notation nhead_any := (nhead_any E pi).
  Notation nest_next := (nest_next E).

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

  Lemma bn_head : forall (Q : machine_state -> Prop) sti st xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m1,
    o_pos sti = pi -> od_plus_k E Q sti -> nest_pre st -> frm0 xfc -> NODh E pi st m1 ->
    (od_head_ok bs idxs 2 st -> nhead_any Q (nest_next st)) ->
    evt bsegs Q (NSTh E ON_HEAD xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m1).
  Proof using OK HLAST HPI HG.
    intros Q sti st xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m1 HSTI HKP [HPOS PRE] FRM INV HEL. unfold ON_HEAD.
    od_env OK.
    assert (DR : (0 <= o_depth st <= o_pos st + 4 /\ o_pos st <= n + 1 /\ (o_err st = 0 \/ o_err st = 3))%Z)
      by (destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & (HP & HPD & HD & HE & HA & HB))|(HE & HD & HP & HA & HB)]]; unfold TAPE_ERROR in *; lia).
    destruct DR as (DR1 & DR2 & DR3).
    pose proof HKP as HKP0. unfold od_plus_k, OD_PLUS in HKP0.
    destruct INV as (j272 & j320 & INV). nod_open INV.

    ostep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep.
    if_cases KD; zify_cond KD; odsig KD.
    -
      destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & PO)|(HE & HD & HP & HA & HB)]]; [exfalso; lia| | exfalso; lia].
      eapply evt_eq; [| eapply (HKP0 st)]; [od_st_eq| split; [lia| left; exact PO]| exact FRM| od_close_inv].
    -
      ostep. ostep. ostep. if_false.
      ostep. ostep. sstep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. gok. ostep. ostep. ostep.
      if_cases KE; zify_cond KE.
      +
        destruct PRE as [HH|[(HD1 & PO)|(HE & HD & HP & HA & HB)]]; [| exfalso; lia| exfalso; unfold TAPE_ERROR in HE; lia].
        eapply evt_eq; [| eapply (bn_elem E OK HLAST pi HPI HG Q st j272)]; [od_st_eq| exact HH| exact HPOS| exact FRM| nod_close| exact (HEL HH)].
      +
        destruct PRE as [(HP & HD & HE & HA & HB)|[(HD1 & (HP & HPD & HD & HE & HA & HB))|(HE & HD & HP & HA & HB)]]; [exfalso; lia| exfalso; lia|].
        pose proof HE as HE3. unfold TAPE_ERROR in HE3.

        ostep. ostep. ostep. if_true. ostep. sstep. ostep. ostep. if_false. sstep. ostep.

        ostep. ostep. ostep. if_false. ostep. ostep. odnorm. ostep. ostep. gok. ostep. ostep.
        if_cases K1; zify_cond K1; [| exfalso; lia]. clear K1.

        ostep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
        ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. if_true.
        eapply evt_eq; [| eapply (HKP0 (o_abandon st))];
          [od_st_eq| split; [cbn [o_abandon o_pos]; lia| right; unfold od_dead; cbn [o_abandon o_alive o_depth o_err o_sbo]; repeat split; assumption]| exact FRM| od_close_inv].
  Qed.

  Lemma bn_loop : forall (Q : machine_state -> Prop) sti, o_pos sti = pi -> od_plus_k E Q sti ->
    forall (fuel : nat) st xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m1,
    (o_left idxs st <= Z.of_nat fuel)%Z -> nest_pre st -> frm0 xfc -> NODh E pi st m1 ->
    evt bsegs Q (NSTh E ON_HEAD xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m1).
  Proof using OK HLAST HPI HG.
    intros Q sti HSTI HKP fuel.
    induction fuel as [|f IH]; intros st xra xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt5 xt6 xF xfc m1 HF PRE FRM INV.
    all: eapply (bn_head Q sti st); [exact HSTI| exact HKP| exact PRE| exact FRM| exact INV|].
    all: intros HH; pose proof HH as (HP & _); unfold o_left in HF.
    - exfalso. lia.
    - intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' NX F' I'.
      destruct PRE as [HPOS _].
      destruct (nest_pre_next st st' HPOS NX) as [PRE' LT].
      apply (IH st'); [unfold o_left; lia| exact PRE'| exact F'| exact I'].
  Qed.
End NestHead.
