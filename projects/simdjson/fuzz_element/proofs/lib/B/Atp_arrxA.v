(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_arrlA Atp_arratA Atp_arrwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition arr_WO (out : Z) : list (Z * Z) := [(out, out + 24)].

Definition arr_ftail (ra s0 s1 s2 s3 s4 s5 pw lw : word) : list cell := [C8 pw; C8 lw; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sub_fp_arrat : forall q out, sub_fp (arrat_W (q + -96) out) (arr_W q out).
Proof. intros q out x Hx. unfold arrat_W, arr_W in *. cbn [outside] in *. lia. Qed.

Lemma arr_frame_canon : forall (m : mem) q pre (ra s0 s1 s2 s3 s4 s5 pw lw : word),
  rw_cells bsegs m (q + -96) pre -> cells_size pre = 24%nat -> rw_cells bsegs m (q + -72) (arr_ftail ra s0 s1 s2 s3 s4 s5 pw lw) ->
  exists jr, rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr).
Proof.
  intros until lw. intros H SZ T. destruct (rw_cells_forget _ _ _ _ H) as [jr H']. rewrite SZ in H'. exists jr.
  unfold arr_frame. change (CB 24 jr :: ?rest) with ([CB 24 jr] ++ rest).
  apply (proj2 (rw_cells_app bsegs m _ [CB 24 jr] _)). split; [exact H'|]. cbn [cells_size csize Nat.add].
  replace (q + -96 + Z.of_nat 24) with (q + -72) by lia. exact T.
Qed.
Lemma arr_frame_split : forall (m : mem) q (ra s0 s1 s2 s3 s4 s5 pw lw : word) jr,
  rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr) ->
  rw_cells bsegs m (q + -96) [CB 24 jr] /\ rw_cells bsegs m (q + -72) (arr_ftail ra s0 s1 s2 s3 s4 s5 pw lw).
Proof.
  intros until jr. intros H. unfold arr_frame in H. change (CB 24 jr :: ?rest) with ([CB 24 jr] ++ rest) in H.
  apply (proj1 (rw_cells_app bsegs m _ [CB 24 jr] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add] in H2.
  replace (q + -96 + Z.of_nat 24) with (q + -72) in H2 by lia. exact (conj H1 H2).
Qed.

Section ArrExits.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma arr_walk2 : forall (K : machine_state -> Prop) (m0 m : mem) (F : bvmap 5 word) (fc : bv 32) (i e c q out node P tok L1 : Z) (idx : word)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j8 oa ob oc od : list byte) (x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
    ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 -> tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    0 <= tok <= L1 -> 0 < P + 1 -> P + 1 + L1 < 2^47 ->
    munch (arr_W q out) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (q + -96) -> ae_lo E + 208 <= q -> q mod 16 = 0 ->
    rw_cells bsegs m (q + -96) [C8 (wz (ae_DOC E)); C8 (wz i); CB 8 j8] ->
    rw_cells bsegs m (q + -72) (arr_ftail ra s0 s1 s2 s3 s4 s5 (wz (P + 1)) (wz L1)) ->
    rw_cells bsegs m out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    (forall m', munch (arr_W q out) m0 m' -> wmono bsegs m0 m' -> AINV_A E m') ->
    (forall m', munch (arr_W q out) m0 m' -> wmono bsegs m0 m' -> shb_cells m') ->
    (forall m', munch (arr_W q out) m0 m' -> wmono bsegs m0 m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (arr_W q out) m0 m' -> wmono bsegs m0 m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch (arr_W q out) m0 m' -> wmono bsegs m0 m' -> shz m' (q + -96) 96) ->
    (forall m', munch (arr_W q out) m0 m' -> wmono bsegs m0 m' -> shz m' out 24) ->

    (forall (m1 : mem) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys7 ys8 ys9 y28 y29 y30 y31 : word) (j0 jr : list byte),
       munch (arr_W q out) m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -192) ->
       rw_cells bsegs m1 (q + -192) (arrat_frame (wz 0xb8f38) (wz out) (wz node) (wz tok) idx (wz 2147450880) (wz 22) s6 s7 s8 s9 j0) ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (wz (P + 1)) (wz L1) jr) ->
       rw_cells bsegs m1 out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
       evt bsegs K (MS (mkR (wz 0xb97ac) (wz (q + -192)) gp (wz TPV) y5 y6 y7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) ya3 ya4 ya5 ya6 ya7
                          ys2 ys3 ys4 ys5 (wz 2147450880) ys7 ys8 ys9 s10 s11 y28 y29 y30 y31)
                     F (wz e_asan_memset) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (it j' : Z) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_W q out) m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) q ->
       elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' -> 0 <= it -> j' <= e ->
       rw_cells bsegs m1 out [C8 (wz (ae_DOC E)); C8 (wz it); C4 (wz 0); CB 4 od] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F (ret_pc ra) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (it j' : Z) (y5 y6 y7 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word) (jr : list byte),
       tok < L1 ->
       munch (arr_W q out) m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' -> 0 <= it -> j' <= e ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (wz (P + 1)) (wz L1) jr) ->
       rw_cells bsegs m1 out [C8 (wz (ae_DOC E)); C8 (wz it); C4 (wz 0); CB 4 od] ->
       evt bsegs K (lvl_entry ATP_ELEM_A (wz 0xb9014) (q + -96) gp y5 y6 y7 (wz out) (wz (out + 16)) (q + -96) out (P + 1 + tok) (L1 - tok)
                       ya4 ya5 ya6 ya7 (wz 0) idx (wz ((out + 16) / 8 + 2147450880)) (wz 22) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 F fc m1)) ->
    evt bsegs K (MS (mkR (wz 0xb8f28) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) (wz node) (wz (q + -96)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (wz tok) idx (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb8f28) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros TY NXT TILES I0 EN TOK P0 PL MU WM MI ST LO Q16 FRn FRt OUT QO OB O8 AIW SHBW SHZDW SHZTW SHZFW SHZOW XASET XDONE XREC.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    unfold arr_W in MU. unfold arr_ftail in FRt.
    assert (Q16' : (q + -96) mod 16 = 0) by (replace (q + -96) with (q + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).

    step. step. step. step.
    pose proof FRn as NODEC. change [C8 (wz (ae_DOC E)); C8 (wz i); CB 8 j8] with ([C8 (wz (ae_DOC E)); C8 (wz i)] ++ [CB 8 j8]) in NODEC.
    apply (proj1 (rw_cells_app bsegs m _ _ _)) in NODEC. destruct NODEC as [NODEC _].
    eapply (arrat_walk E OK d K m F fc i e c (q + -96) out 0xb8f38 idx);
      [ exact TY| exact NXT| exact TILES| exact I0| exact EN| exact NODEC| exact OUT| lia| exact OB| exact O8
      | intros m' MU' WM'; exact (AIW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_arrat q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | intros m' MU' WM'; exact (SHBW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_arrat q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | intros m' MU' WM'; exact (SHZDW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_arrat q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | intros m' MU' WM'; exact (SHZTW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_arrat q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | intros m' MU' WM'; apply (shz_sub m' (q + -96) 96); [exact (SHZFW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_arrat q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
      | intros m' MU' WM'; exact (SHZOW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_arrat q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))
      | exact ST| lia| lia| exact Q16'| exact MI| lia| reflexivity| | ].
    {
      clear ST MI. intros m1 y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys7 ys8 ys9 y28 y29 y30 y31 j0 MUa WMa MI1 ST1 FRA OUT1.
      unfold arrat_W in MUa. hide OUT. clear NODEC. transport_after_call bsegs m m1 MUa WMa. clear MUa WMa OUT.
      destruct (arr_frame_canon m1 q _ ra s0 s1 s2 s3 s4 s5 _ _ FRn eq_refl FRt) as [jr FR1].
      replace (q + -96 + -96) with (q + -192) in ST1, FRA by lia.
      eapply evt_eq; [| eapply XASET]; [atp_st_eq| exact MU| exact WM| exact MI1| exact ST1| exact FRA| exact FR1| exact OUT1]. }

    clear ST MI. intros m1 it j' y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 MUa WMa MI1 ST1 EL IT0 JE OUT1.
    unfold arrat_W in MUa. hide OUT. clear NODEC. transport_after_call bsegs m m1 MUa WMa. clear MUa WMa OUT.

    step. if_dead1 by QO LO LOW. astep. astep. astep.
    shz_pose SHZOW (out + 16). step. shz_norm. step. if_false.
    astep. astep. step. if_false. step. if_false.
    step. step. if_cases KT; zify_cond KT.
    {
      destruct (arr_frame_canon m1 q _ ra s0 s1 s2 s3 s4 s5 _ _ FRn eq_refl FRt) as [jr FR1].
      eapply (arr_epi K m1 F fc q (ae_lo E) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ jr); [exact FR1| exact ST1| exact MI1| lia|].
      intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ST'. eapply (XDONE m1 it j'); [exact MU| exact WM| exact MI1| exact ST'| exact EL| exact IT0| exact JE| exact OUT1]. }

    astep. astep. step. step.
    pose proof FRt as SV1. change (C8 (wz (P + 1)) :: C8 (wz L1) :: ?rest) with ([C8 (wz (P + 1)); C8 (wz L1)] ++ rest) in SV1.
    apply (proj1 (rw_cells_app bsegs m1 _ _ _)) in SV1. destruct SV1 as [SV1 _].
    hide FRn. hide FRt. hide OUT1.
    eapply evt_eq; [| eapply (substr_cps E OK K m1 F fc (q + -96) (q + -72) (P + 1) L1 tok 18446744073709551615 (L1 - tok) 0xb8f78);
      [ exact SV1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| lia| lia| lia| left; split; reflexivity| exact (SHBW m1 MU WM)
      | intros m' MU' WM'; apply (shz_sub m' (q + -96) 96); [exact (SHZFW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_lvl16 q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
      | exact ST1| lia| lia| exact Q16'| exact MI1| lia| reflexivity| ] ]; [atp_st_eq|].
    clear ST1 MI1 SV1. intros m2 xb2 xb3 xb4 xb5 MU12 WM12 MI2 ST2.
    unhide FRn. unhide FRt. unhide OUT1.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.

    step. step.
    shz_pose SHZOW (out + 16). step. shz_norm. step. if_false.
    astep. astep. step. if_false. astep. step. if_true. step. step.
    destruct (arr_frame_canon m2 q _ ra s0 s1 s2 s3 s4 s5 _ _ FRn eq_refl FRt) as [jr FR2].
    eapply evt_eq; [| eapply (XREC m2 it j')]; [unfold lvl_entry, ATP_ELEM_A; atp_st_eq| exact KT| exact MU| exact WM| exact MI2| exact ST2| exact EL| exact IT0| exact JE| exact FR2| exact OUT1].
  Qed.

  Lemma arr_after_aset : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out node tok : Z) (idx : word)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw : word) (j0 jr zb j1 j2 : list byte)
      (x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -192) (arrat_frame (wz 0xb8f38) (wz out) (wz node) (wz tok) idx (wz 2147450880) (wz 22) s6 s7 s8 s9 j0) ->
    rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr) ->
    stk bsegs m (ae_lo E) (q + -192) -> mem_inv bsegs m -> ae_lo E + 208 <= q ->
    rw_cells bsegs m out [CB 16 zb; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    (forall m', munch (arr_WO out) m m' -> wmono bsegs m m' -> shz m' out 24) ->
    (forall (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_WO out) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 zb; C4 (Z_to_bv 64 19); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb97ac) (wz (q + -192)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 xs4 xs5 (wz 2147450880) xs7 xs8 xs9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb97ac) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FRA FR ST MI LO OUT QO OB O8 SHZO HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    unfold arr_WO in SHZO, HK.
    replace (q + -192) with (q + -96 + -96) in FRA, ST |- * by lia.
    eapply (arrat_after_set E OK K m F fc (q + -96) out 0xb8f38); [exact FRA| exact ST| exact MI| lia| exact OUT| lia| exact OB| exact O8| exact (SHZO m (munch_refl _ m) (wmono_refl bsegs m))| lia| reflexivity|].
    clear ST MI. intros m1 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 MU1 WM1 MI1 ST1 OUT1.
    pose proof (rw_cells_transport bsegs _ m m1 _ _ FR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add arr_frame length fst snd]; lia)) as FR1.
    pose proof MU1 as MU. pose proof WM1 as WM.

    step. if_dead1 by QO LO LOW. astep. astep. astep.
    shz_pose SHZO (out + 16). step. shz_norm. step. if_false.
    astep. astep. step. if_false. step. if_true.
    apply (arr_epi K m1 F fc q (ae_lo E) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw jr); [exact FR1| exact ST1| exact MI1| lia|].
    intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ST'. eapply (HK m1); [exact MU1| exact WM1| exact MI1| exact ST'| exact OUT1].
  Qed.

  Lemma arr_after_cpy : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw : word) (jr b16 j1 j2 : list byte)
      (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr) -> stk bsegs m (ae_lo E) (q + -96) -> mem_inv bsegs m -> ae_lo E <= q + -96 ->
    rw_cells bsegs m out [CB 16 b16; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 ->
    (forall (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_WO out) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 b16; C4 (Z_to_bv 64 0); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb8df8) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 (wz 2147450880) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb8df8) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (arr_WO out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold arr_WO in MU. unfold arr_frame in FR.

    astep. chk0 SHZO (out + 16). step. if_false. lstep. step.
    name_mem m1.
    apply (arr_epi K m1 F fc q (ae_lo E) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw jr); [unfold arr_frame; assumption| assumption| assumption| exact LO|].
    intros until y31. intros ST'.
    lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    apply (HK m1); [exact MU| exact WM| exact MI1| exact ST'| exact OUT1].
  Qed.

  Lemma arr_after_set : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out ra' code : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw s5' xs2 xs3 : word) (jr zb j1 j2 : list byte)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr) -> stk bsegs m (ae_lo E) (q + -96) -> mem_inv bsegs m -> ae_lo E <= q + -96 ->
    rw_cells bsegs m out [CB 16 zb; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 -> arr_set_site ra' s5' code ->
    (forall (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_WO out) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 zb; C4 (Z_to_bv 64 code); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz ra') (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) x11 x12 x13 x14 x15 x16 x17
                       xs2 xs3 (wz 2147450880) s5' s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz ra') fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO SITE HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (arr_WO out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold arr_WO in MU. unfold arr_frame in FR.
    assert (EPI : forall (m1 : mem) (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z28 z29 z30 z31 : word),
      munch [(out, out + 24)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
      rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr) -> stk bsegs m1 (ae_lo E) (q + -96) ->
      rw_cells bsegs m1 out [CB 16 zb; C4 (Z_to_bv 64 code); CB 4 j2] ->
      evt bsegs K (MS (mkR z1 (wz (q + -96)) gp (wz TPV) z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                      F (wz 0xb8fe8) fc None m1 (seg_rom bsegs))).
    { intros until z31. intros MU1 WM1 MI1 FR1 ST1 OUT1.
      apply (arr_epi K m1 F fc q (ae_lo E) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw jr); [exact FR1| exact ST1| exact MI1| exact LO|].
      intros until y31. intros ST'. apply (HK m1); [exact MU1| exact WM1| exact MI1| exact ST'| exact OUT1]. }
    destruct SITE as [(-> & ->)|[(-> & -> & ->)|(-> & -> & CODE)]].
    -
      chk0 SHZO (out + 16). step. if_false. astep. lstep. step.
      eapply EPI; [exact MU| exact WM| assumption| unfold arr_frame; assumption| assumption| assumption].
    -
      chk0 SHZO (out + 16). step. if_false. astep. step. lstep. step.
      eapply EPI; [exact MU| exact WM| assumption| unfold arr_frame; assumption| assumption| assumption].
    -
      assert (CR : 0 <= code < 2^32) by lia.
      chk0 SHZO (out + 16). step. if_false. lstep.
      eapply EPI; [exact MU| exact WM| assumption| unfold arr_frame; assumption| assumption| assumption].
  Qed.

  Lemma arr_rec_glue : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out : Z)
      (gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word),
    mem_inv bsegs m -> 0x649000 <= q + -96 -> q <= 2^47 ->
    K (MS (mkR (wz 0xb9024) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 (wz out) (wz (q + -96)) (wz 16) x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR (wz 0xb9014) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb9014) fc None m (seg_rom bsegs)).
  Proof.
    intros until x31. intros MI QL QH HK.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    step. astep. step. step.
    eapply evt_eq; [| apply evt_done; exact HK]. unfold e_asan_memcpy. atp_st_eq.
  Qed.

  Lemma arr_after_rec : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out code : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw r0 rj : word) (jn b16 j2 : list byte)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -96) [C8 r0; C8 rj; C4 (Z_to_bv 64 code); CB 4 jn] -> rw_cells bsegs m (q + -72) (arr_ftail ra s0 s1 s2 s3 s4 s5 pw lw) ->
    stk bsegs m (ae_lo E) (q + -96) -> mem_inv bsegs m -> ae_lo E <= q + -96 ->
    rw_cells bsegs m out [CB 16 b16; C4 (Z_to_bv 64 0); CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 -> 0 <= code < 64 ->
    (forall (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_WO out) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 b16; C4 (Z_to_bv 64 code); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb9024) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 (wz ((out + 16) / 8 + 2147450880)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb9024) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FRr FRt ST MI LO OUT QO OB O8 SHZO CODE HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (arr_WO out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold arr_WO in MU. unfold arr_ftail in FRt.

    astep. astep. step. if_dead1 by CODE.
    shz_pose SHZO (out + 16). step. shz_norm. step. if_true.
    lstep. step.
    name_mem m1.
    lazymatch goal with H : rw_cells bsegs m1 (q + -96) _ |- _ => rename H into FRr1 end.
    lazymatch goal with H : rw_cells bsegs m1 (q + -72) _ |- _ => rename H into FRt1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.
    destruct (arr_frame_canon m1 q _ ra s0 s1 s2 s3 s4 s5 pw lw FRr1 eq_refl FRt1) as [jr FR1].
    apply (arr_epi K m1 F fc q (ae_lo E) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw jr); [exact FR1| exact ST1| exact MI1| exact LO|].
    intros until y31. intros ST'. eapply (HK m1); [exact MU| exact WM| exact MI1| exact ST'| exact OUT1].
  Qed.
End ArrExits.
