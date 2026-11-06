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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_nest_plusB Od_nest_firstB Od_nest_elemB Od_nest_headB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section NestSetup.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Variable pi : Z.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Lemma bn_setup : forall (Q : machine_state -> Prop) stb d' xra xt0 xt2 xa2 xa3 xa4 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1,
    ODINVg E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 (o_IDX E + 4 * pi) stb m1 -> (1 <= d' <= 3)%Z -> frm0 xfc ->
    nhead_any E pi Q (fun st' => st' = o_setd stb d') ->
    evt bsegs Q (ODST E 0x99a38 xra xt0 (Z_to_bv 64 (o_IDX E + 4 * pi)) xt2 (Z_to_bv 64 d') (Z_to_bv 64 (oa_F E + 228)) xa2 xa3 xa4
                      (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) xa6 xa7
                      xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK.
    intros Q stb d' xra xt0 xt2 xa2 xa3 xa4 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 INV HD' FRM HK.
    od_open_inv INV. od_env OK. unfold nhead_any, ON_HEAD in HK.

    ostep. ostep. if_true. sstep. sstep. ostep. ostep. ostep. ostep. sstep. ostep. ostep. ostep. sstep. ostep. sstep. ostep. ostep. sstep. ostep. sstep. sstep.
    eapply evt_eq; [| eapply (HK (o_setd stb d'))]; [od_st_eq| reflexivity| exact FRM| nodh_close].
  Qed.
End NestSetup.

Section Arm.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HG : od_shb E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Theorem od_arm_nest : arm_stmt E 0x97754.
  Proof using OK HG.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (HD2 : o_depth st = 2%Z) by lia.
    assert (HPI : (1 <= o_pos st)%Z) by lia.
    od_open_inv INV. od_env OK. rewrite HD2 in ITER.
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

    assert (K_SET : forall stb d', (o_pos st < o_pos stb)%Z -> (1 <= d' <= 3)%Z -> nest_pre E (o_pos st) (o_setd stb d') ->
              forall yra yt0 yt2 ya2 ya3 ya4 ya6 ya7 ys2 ys5 ys6 ys10 yt3 yt5 yt6 mm,
              ODINVg E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 (o_IDX E + 4 * o_pos st) stb mm ->
              evt bsegs Q (ODST E 0x99a38 yra yt0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) yt2 (Z_to_bv 64 d') (Z_to_bv 64 (oa_F E + 228)) ya2 ya3 ya4
                                (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) ya6 ya7
                                ys2 ys5 ys6 ys10 (Z_to_bv 64 (oa_F E + 192)) yt3 (Z_to_bv 64 2) yt5 yt6 xF xfc mm)).
    { intros stb d' HPB HD' PRE yra yt0 yt2 ya2 ya3 ya4 ya6 ya7 ys2 ys5 ys6 ys10 yt3 yt5 yt6 mm INV2.
      eapply (bn_setup E OK (o_pos st) Q stb d'); [exact INV2| exact HD'| exact FRM|].
      intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' -> F' I'.
      eapply (bn_loop E OK HLAST (o_pos st) HPI HG Q st eq_refl HK (Z.to_nat (n + 1)) (o_setd stb d')); [| exact PRE| exact F'| exact I'].
      unfold o_left. destruct PRE as [PP _]. cbn [o_setd o_pos] in *. lia. }

    zstep. if_false.
    ostep. ostep. gtrap. ostep. ual. ostep. gtrap. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. if_true.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. gok. ostep. gok. ostep. ostep. ostep. if_true. ostep. gok. ostep. ual. ostep. gok.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. gok. ostep. ostep. ostep. unz. ostep. gok. ostep. gok.
    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep.
    if_cases K; zify_cond K.
    -
      clear K_SET.
      ostep. sstep. ostep. ostep. ostep. ostep. ostep. ostep. sstep. ostep. ostep. ostep. sstep. ostep. sstep. ostep. ostep. sstep. ostep. sstep. sstep.

      ostep. if_true. ostep. ostep. ostep. if_true.
      ostep. if_true. ostep. ostep. ostep. if_false. ostep.
      eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      ostep. gok. ostep. ostep. gok. ostep. ostep. if_true. ostep. ostep.
      clear RD1 RD2.
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (tokI bs idxs (o_pos st + 1)) BUFRO ltac:(lia)) as RD4).
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st + 1) IDXA (conj IDXL IDXF) ltac:(lia)) as RD3).
      fold (tokT bs idxs (o_pos st + 1)) in RD4. fold c1 in RD4.
      replace (o_IDX E + 4 * (o_pos st + 1))%Z with (o_IDX E + 4 * o_pos st + 4)%Z in RD3 by lia.
      set (off1 := tokI bs idxs (o_pos st + 1)) in *.
      od_cur_mem ltac:(fun mm => assert (INV1 : ODINVg E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 (o_IDX E + 4 * o_pos st) (o_adv st 1) mm) by od_close_inv).

      ostep. gok. ostep. ostep. gok. ostep. ostep. gok. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. gok. ostep. gok.
      ostep. ostep. ostep. if_true. ostep. ual. ostep. gok. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. gok.
      ostep. ostep. ostep. unz. ostep. gok. ostep. gok. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep.
      assert (SA : start_array bs idxs 1 st = if (c1 =? 93)%Z then (o_setd (o_adv st 2) 1, true) else (o_setd (o_adv st 1) 3, true)).
      { unfold start_array. fold c. fold c1. unfold C_LBRACKET, C_RBRACKET. rewrite (proj2 (Z.eqb_eq c 91)) by lia. reflexivity. }
      if_cases K2; zify_cond K2.
      +
        ostep. gok. ostep. gok. ostep. ostep. gok. ostep. ostep. if_true. ostep. ostep. ostep. ostep. gok. ostep. ostep.
        eapply evt_eq; [| eapply (K_SET (o_adv st 2) 1%Z); [cbn [o_adv o_pos]; lia| lia| | od_close_inv]]; [od_st_eq|].
        split; [cbn [o_setd o_adv o_pos]; lia|]. right; left. split; [reflexivity|].
        pose proof (acc_plus_ok bs idxs S1 HLAST 1 st _ ltac:(lia) HH (acc_array bs idxs 1 st)) as PO.
        rewrite SA in PO. rewrite (proj2 (Z.eqb_eq c1 93)) in PO by lia. exact PO.
      +
        ostep. ostep. ostep. gok. ostep. ostep. gok. ostep. ostep. gok.
        eapply evt_eq; [| eapply (K_SET (o_adv st 1) 3%Z); [cbn [o_adv o_pos]; lia| lia| | exact INV1]]; [od_st_eq|].
        split; [cbn [o_setd o_adv o_pos]; lia|]. left.
        apply (od_inner_head_ok bs idxs S1 HLAST 1 st ltac:(lia) HH); [unfold C_LBRACKET; fold c; lia| unfold C_RBRACKET; fold c1; lia].
  Qed.
End Arm.
