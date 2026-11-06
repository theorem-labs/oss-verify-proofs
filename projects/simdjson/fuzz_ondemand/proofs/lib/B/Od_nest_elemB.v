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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_tablesB Od_nest_plusB Od_nest_firstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section NestElem.
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

  Definition nest_next (st st' : ost) : Prop :=
    od_next_ok bs idxs 2 st st' \/ od_next_ok bs idxs 2 (consume 2 st) st'.

  Local Ltac bload m1 BUFRO k :=
    let RB := fresh "RB" in
    pose proof (tokB_read m1 E k BUFRO ltac:(lia)) as RB; ostep; odnorm; clear RB.

  Lemma bn_elem : forall (Q : machine_state -> Prop) st j272 xra xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xt3 xt5 xt6 xF xfc m1,
    od_head_ok bs idxs 2 st -> (pi < o_pos st)%Z -> frm0 xfc ->
    NODb E pi (CB 8 j272) (C8 (wz ((oa_F E + 224) / 8 + 2147450880))) st m1 ->
    nhead_any Q (nest_next st) ->
    evt bsegs Q (NSTh E 0x99b20 xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 ((oa_F E + 208) / 8)) xa5 xa6 xa7 (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) xs5
                      xt3 xt5 xt6 xF xfc m1).
  Proof using OK HLAST HPI HG.
    intros Q st j272 xra xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xs5 xt3 xt5 xt6 xF xfc m1 HH HPP FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (HD3 : o_depth st = 3%Z) by lia.
    od_env OK.

    pose proof (acc_plus_ok bs idxs S1 HLAST 2 st st ltac:(lia) HH (acc_none bs idxs 2 st)) as PO0.
    pose proof (acc_plus_ok bs idxs S1 HLAST 2 st (consume 2 st) ltac:(lia) HH (acc_scalar bs idxs 2 st)) as PO1.
    assert (K_NONE : forall yra ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys3 ys4 ys8 yt0,
              evt bsegs Q (NSTb E 0x99dd0 yra yt0 xt1 xt2 ya0 ya1 ya2 ya3 (Z_to_bv 64 ((oa_F E + 208) / 8)) ya5 ya6 ya7
                                (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) ys3 ys4 xs5 ys8 (Z_to_bv 64 4) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1)).
    { intros. eapply (bn_plus E OK HLAST pi HPI HG Q st); [exact PO0| exact HPP| exact FRM| exact INV|].
      intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' P' F' I'. apply (HK st'); [left; exact P'| exact F'| exact I']. }
    assert (K_CONS : forall yra ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys3 ys4 ys8 yt0 mm, NODb E pi (CB 8 j272) (C8 (wz ((oa_F E + 224) / 8 + 2147450880))) (consume 2 st) mm ->
              evt bsegs Q (NSTb E 0x99dd0 yra yt0 xt1 xt2 ya0 ya1 ya2 ya3 (Z_to_bv 64 ((oa_F E + 208) / 8)) ya5 ya6 ya7
                                (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) ys3 ys4 xs5 ys8 (Z_to_bv 64 4) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc mm)).
    { intros yra ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys3 ys4 ys8 yt0 mm INV2.
      eapply (bn_plus E OK HLAST pi HPI HG Q (consume 2 st)); [exact PO1| cbn [consume o_setd o_adv o_pos]; lia| exact FRM| exact INV2|].
      intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' P' F' I'. apply (HK st'); [right; exact P'| exact F'| exact I']. }
    clear PO0 PO1.
    nod_open INV. rewrite HD3 in ITER.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0. pose proof (od_B_range E BOK (off + 1)) as R1.
    pose proof (od_B_range E BOK (off + 2)) as R2. pose proof (od_B_range E BOK (off + 3)) as R3.
    pose proof (od_B_range E BOK (off + 4)) as R4.
    set (b0 := B bs off) in *. set (b1 := B bs (off + 1)) in *. set (b2 := B bs (off + 2)) in *.
    set (b3 := B bs (off + 3)) in *. set (b4 := B bs (off + 4)) in *.

    ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. gok. ostep. ostep. gok. ostep. ostep. if_false. ostep. gok. ostep. odnorm. ostep. ostep. gok.
    ostep. ostep. if_true. ostep. ostep. if_true.

    ostep. ostep. if_false. ostep. odnorm. ostep. gok. ostep. gok. ostep. ostep. gok. ostep. ostep. ostep. ostep. if_true. ostep. ual. ostep. gok.
    ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. clear RD1. ostep. ostep. gok. ostep. ostep. ostep. unz. ostep. gok.
    ostep. ostep. ostep. ostep. if_false. ostep. ostep. ostep. ostep. ostep. if_false.

    bload m1 BUFRO (off + 1)%Z. bload m1 BUFRO off. bload m1 BUFRO (off + 2)%Z. bload m1 BUFRO (off + 3)%Z.
    ostep. ostep. ostep. ostep. ostep. ostep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let w := fresh "w" in set (w := Z_to_bv 64 (Z.lor x y)) in *; clearbody w end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => let w := fresh "v" in set (w := Z_to_bv 64 (Z.shiftl x y)) in *; clearbody w end.
    ostep. zstep.
    if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply K_NONE]. od_st_eq.
    -
      clear K.
      ostep. ostep. gok. ostep. ostep. ostep. ostep. if_false. ostep. ostep.
      bload m1 BUFRO (off + 4)%Z.
      pose proof (bsow_read m1 b4 MI ltac:(lia)) as RT4. pose proof (osow_range b4) as RS4. unfold BT_SOW in RT4.
      ostep. ostep. gok. ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. gok. zstep.
      if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply K_NONE]. od_st_eq.
      +
        clear K2 RT4.
        ostep. ostep. if_true. ostep. ostep. if_false.

        ostep. ostep. if_false. ostep. odnorm. ostep. gok. ostep. gok. ostep. ostep. gok. ostep. ostep. ostep. ostep. if_true. ostep. ostep. gok.
        ostep. ostep. if_true. ostep. ostep. ostep. ual. ostep.

        od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
        fold off in RD3.
        ostep. gok. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. gok. ostep. ostep. ostep. unz. ostep. gok.
        ostep. ostep. gok. ostep. ostep. if_false. ostep. ostep.
        eapply evt_eq; [| eapply K_CONS; nod_close]. od_st_eq.
  Qed.
End NestElem.
