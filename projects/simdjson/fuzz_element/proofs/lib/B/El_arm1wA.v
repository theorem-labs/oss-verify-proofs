(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_arrlA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA El_armkit2A El_haccA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition gw_W (q out : Z) : list (Z * Z) := [(q + -80, q); (out, out + 24)].
Definition gw_frame (ra s0 s1 s2 s3 s4 s5 : word) (j0 : list byte) : list cell := [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma sub_fp_gw_tix : forall q out, sub_fp [(q + -64 + -16, q + -64)] (gw_W q out).
Proof. intros q out x Hx. unfold gw_W in *. cbn [outside] in *. lia. Qed.

Section W1.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma garr_walk1 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q node out RA : Z) (jr : list byte)
      (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    stk bsegs m (ae_lo E) q -> ae_lo E + 80 <= q -> q <= ae_hi E -> q mod 16 = 0 -> mem_inv bsegs m ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < node -> node + 16 <= q + -80 ->
    rw_cells bsegs m out [CB 24 jr] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall m', munch (gw_W q out) m m' -> AINV_A E m') ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shb_cells m') ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' node 16) ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' out 24) ->

    (forall (m1 : mem) (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x28 x29 x30 x31 : word) (j4 : list byte),
       munch (gw_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) q ->
       rw_cells bsegs m1 out [C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j4] ->
       evt bsegs K (MS (mkR (wz RA) (wz q) gp (wz TPV) x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz RA) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (x5 x6 x7 xa3 xa4 x28 x29 x30 x31 : word) (j0 : list byte),
       munch (gw_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -64) ->
       rw_cells bsegs m1 (q + -64) (gw_frame (wz RA) s0 s1 s2 s3 s4 s5 j0) -> rw_cells bsegs m1 out [CB 24 jr] ->
       evt bsegs K (MS (mkR (wz 0xb2d7c) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) xa3 xa4 a5 a6 a7
                         (wz (node + 8)) (wz SHB) (wz (shad node)) (wz (shad (node + 8))) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz e_asan_memset) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz q) gp (wz TPV) t0 t1 t2 s0 s1 (wz out) (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0xb2c74) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros ST LO HI Q16 MI NODE N0 NQ OUT QO OH O8 RA0 RA2 AIW SHBW SZN SZD SZT SZO XOK XNA.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP, SHB in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl (gw_W q out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold gw_W in MU.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 7 lstep.
    pose proof (SHBW _ MU WM) as [G1 G2].
    astep. step. step.
    name_mem m1.

    astep. chk0 SZN node. step. if_false.
    astep. step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
    astep. chk0 SZN (node + 8). step. if_false. step. zstep.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (q + -64) 1 0xb2ce4); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_gw_tix q out) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB1.

    chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
    replace (ae_TAPE E + 8 * 1 + 7) with (ae_TAPE E + 8 * 1 + 7) in RDB1 by lia. step. astep.
    lazymatch goal with H : rw_cells bsegs m2 (q + -64) _ |- _ => rename H into FR2 end.
    lazymatch goal with H : rw_cells bsegs m2 out _ |- _ => rename H into OUT2 end.
    step. if_cases K1; zify_cond K1.
    -
      step. if_dead1 by QO LO LOW. astep. astep. astep. astep. zstep.
      eapply evt_eq; [| eapply (XNA m2)]; [unfold e_asan_memset; atp_st_eq| exact MU| exact WM| exact MI2| exact ST2| unfold gw_frame; exact FR2| exact OUT2].
    -
      step. if_dead1 by QO LO LOW.
      shz_pose SZN (node + 8). step. shz_norm. step. if_false.
      shz_pose SZN node. step. shz_norm. step. if_false.
      chk0 SZO out. step. if_false.

      apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 4; 4]%nat) in OUT2; [| reflexivity]. cbn [mk_CB_cells app] in OUT2.
      step. step. astep. lstep.
      chk0 SZO (out + 8). step. if_false. lstep.
      astep. chk0 SZO (out + 16). step. if_false. lstep. zstep.
      name_mem mF.
      lazymatch goal with H : rw_cells bsegs mF (q + -64) _ |- _ => rename H into FRF end.
      lazymatch goal with H : stk bsegs mF _ _ |- _ => rename H into STF end.

      do 7 step. astep. release_frame FRF STF q. step.
      replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      lazymatch goal with H : stk bsegs mF _ q |- _ => rename H into STF' end.
      lazymatch goal with H : mem_inv bsegs mF |- _ => rename H into MIF end.
      lazymatch goal with H : rw_cells bsegs mF out _ |- _ => rename H into OUTF end.
      lazymatch goal with H : munch _ m mF |- _ => rename H into MUF end.
      lazymatch goal with H : wmono bsegs m mF |- _ => rename H into WMF end.
      eapply evt_eq; [| eapply (XOK mF)]; [atp_st_eq| exact MUF| exact WMF| exact MIF| exact STF'| exact OUTF].
  Qed.

  Lemma garr_after_set : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out RA : Z) (j0 zb j1 j2 : list byte)
      (gp x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s0 s1 s2 s3 s4 s5 xs2 xs4 xs5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -64) (gw_frame (wz RA) s0 s1 s2 s3 s4 s5 j0) -> stk bsegs m (ae_lo E) (q + -64) -> ae_lo E + 80 <= q -> q <= ae_hi E -> mem_inv bsegs m ->
    rw_cells bsegs m out [CB 16 zb; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> shz m out 24 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem), munch [(out, out + 24)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 zb; C4 (wz 17); CB 4 j2] ->
       evt bsegs K (MS (mkR (wz RA) (wz q) gp (wz TPV) x5 x6 x7 s0 s1 (wz 17) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb2d7c) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 (wz SHB) xs4 xs5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb2d7c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST LO HI MI OUT QO OH SHZO RA0 RA2 HK. unfold gw_frame, SHB in *.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    chk0 SHZO (out + 16). step. if_false. astep. lstep.
    name_mem m1.
    lazymatch goal with H : rw_cells bsegs m1 (q + -64) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    do 7 step. astep. release_frame FR1 ST1 q. step.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
    lazymatch goal with H : stk bsegs m1 _ q |- _ => rename H into ST1' end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.
    eapply (HK m1); [exact MU| exact WM| exact MI1| exact ST1'| exact OUT1].
  Qed.

  Lemma gobj_walk1 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q node out RA : Z) (jr : list byte)
      (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    stk bsegs m (ae_lo E) q -> ae_lo E + 80 <= q -> q <= ae_hi E -> q mod 16 = 0 -> mem_inv bsegs m ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < node -> node + 16 <= q + -80 ->
    rw_cells bsegs m out [CB 24 jr] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall m', munch (gw_W q out) m m' -> AINV_A E m') ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shb_cells m') ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' node 16) ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch (gw_W q out) m m' -> wmono bsegs m m' -> shz m' out 24) ->

    (forall (m1 : mem) (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x28 x29 x30 x31 : word) (j4 : list byte),
       munch (gw_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) q ->
       rw_cells bsegs m1 out [C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j4] ->
       evt bsegs K (MS (mkR (wz RA) (wz q) gp (wz TPV) x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz RA) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (x5 x6 x7 xa3 xa4 x28 x29 x30 x31 : word) (j0 : list byte),
       munch (gw_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -64) ->
       rw_cells bsegs m1 (q + -64) (gw_frame (wz RA) s0 s1 s2 s3 s4 s5 j0) -> rw_cells bsegs m1 out [CB 24 jr] ->
       evt bsegs K (MS (mkR (wz 0xb2f18) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) xa3 xa4 a5 a6 a7
                         (wz (node + 8)) (wz SHB) (wz (shad node)) (wz (shad (node + 8))) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz e_asan_memset) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz q) gp (wz TPV) t0 t1 t2 s0 s1 (wz out) (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0xb2e10) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros ST LO HI Q16 MI NODE N0 NQ OUT QO OH O8 RA0 RA2 AIW SHBW SZN SZD SZT SZO XOK XNA.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP, SHB in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl (gw_W q out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold gw_W in MU.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 7 lstep.
    pose proof (SHBW _ MU WM) as [G1 G2].
    astep. step. step.
    name_mem m1.

    astep. chk0 SZN node. step. if_false.
    astep. step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
    astep. chk0 SZN (node + 8). step. if_false. step. zstep.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (q + -64) 1 0xb2e80); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_gw_tix q out) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB1.

    chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
    replace (ae_TAPE E + 8 * 1 + 7) with (ae_TAPE E + 8 * 1 + 7) in RDB1 by lia. step. astep.
    lazymatch goal with H : rw_cells bsegs m2 (q + -64) _ |- _ => rename H into FR2 end.
    lazymatch goal with H : rw_cells bsegs m2 out _ |- _ => rename H into OUT2 end.
    step. if_cases K1; zify_cond K1.
    -
      step. if_dead1 by QO LO LOW. astep. astep. astep. astep. zstep.
      eapply evt_eq; [| eapply (XNA m2)]; [unfold e_asan_memset; atp_st_eq| exact MU| exact WM| exact MI2| exact ST2| unfold gw_frame; exact FR2| exact OUT2].
    -
      step. if_dead1 by QO LO LOW.
      shz_pose SZN (node + 8). step. shz_norm. step. if_false.
      shz_pose SZN node. step. shz_norm. step. if_false.
      chk0 SZO out. step. if_false.

      apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 4; 4]%nat) in OUT2; [| reflexivity]. cbn [mk_CB_cells app] in OUT2.
      step. step. astep. lstep.
      chk0 SZO (out + 8). step. if_false. lstep.
      astep. chk0 SZO (out + 16). step. if_false. lstep. zstep.
      name_mem mF.
      lazymatch goal with H : rw_cells bsegs mF (q + -64) _ |- _ => rename H into FRF end.
      lazymatch goal with H : stk bsegs mF _ _ |- _ => rename H into STF end.

      do 7 step. astep. release_frame FRF STF q. step.
      replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      lazymatch goal with H : stk bsegs mF _ q |- _ => rename H into STF' end.
      lazymatch goal with H : mem_inv bsegs mF |- _ => rename H into MIF end.
      lazymatch goal with H : rw_cells bsegs mF out _ |- _ => rename H into OUTF end.
      lazymatch goal with H : munch _ m mF |- _ => rename H into MUF end.
      lazymatch goal with H : wmono bsegs m mF |- _ => rename H into WMF end.
      eapply evt_eq; [| eapply (XOK mF)]; [atp_st_eq| exact MUF| exact WMF| exact MIF| exact STF'| exact OUTF].
  Qed.

  Lemma gobj_after_set : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out RA : Z) (j0 zb j1 j2 : list byte)
      (gp x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s0 s1 s2 s3 s4 s5 xs2 xs4 xs5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -64) (gw_frame (wz RA) s0 s1 s2 s3 s4 s5 j0) -> stk bsegs m (ae_lo E) (q + -64) -> ae_lo E + 80 <= q -> q <= ae_hi E -> mem_inv bsegs m ->
    rw_cells bsegs m out [CB 16 zb; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> shz m out 24 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem), munch [(out, out + 24)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 zb; C4 (wz 17); CB 4 j2] ->
       evt bsegs K (MS (mkR (wz RA) (wz q) gp (wz TPV) x5 x6 x7 s0 s1 (wz 17) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb2f18) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 (wz SHB) xs4 xs5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb2f18) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST LO HI MI OUT QO OH SHZO RA0 RA2 HK. unfold gw_frame, SHB in *.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    chk0 SHZO (out + 16). step. if_false. astep. lstep.
    name_mem m1.
    lazymatch goal with H : rw_cells bsegs m1 (q + -64) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    do 7 step. astep. release_frame FR1 ST1 q. step.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
    lazymatch goal with H : stk bsegs m1 _ q |- _ => rename H into ST1' end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.
    eapply (HK m1); [exact MU| exact WM| exact MI1| exact ST1'| exact OUT1].
  Qed.

End W1.
