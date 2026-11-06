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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_elemxA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section SvFind.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma svfind_cps : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (sp SV A n c RA : Z)
      (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells bsegs m SV [C8 (wz A); C8 (wz n)] -> sp <= SV -> SV + 16 <= ae_hi E -> SV mod 8 = 0 ->
    0 < A -> 0 <= n -> A + n < 2^47 -> 0 <= c < 256 ->
    shb_cells m -> (forall m', munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> shz m' SV 16) ->
    stk bsegs m (ae_lo E) sp -> ae_lo E + 16 <= sp -> sp <= ae_hi E -> sp mod 16 = 0 -> mem_inv bsegs m ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->

    (forall (m' : mem) (xa1 xa2 xa4 xa5 : word), n = 0 -> munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) sp ->
       evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz 18446744073709551615) xa1 xa2 (wz n) xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz RA) fc None m' (seg_rom bsegs))) ->

    (forall (m' : mem) (xa3 xa4 xa5 : word), 0 < n -> munch [(sp + -16, sp)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) (sp + -16) ->
       rw_cells bsegs m' (sp + -16) [C8 s0; C8 (wz RA)] ->
       evt bsegs K (MS (mkR (wz 0xb915c) (wz (sp + -16)) gp (wz TPV) t0 t1 t2 (wz A) s1 (wz A) (wz c) (wz n) xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz e_memchr) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz SV) (wz c) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ATP_SVFIND_A) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros SVC QS SH S8 A0 N0 AN CR [G1 G2] SHZS ST LO HI S16 MI RA0 RA2 XNPOS XCHR.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    unfold ATP_SVFIND_A, SEGTOP_A, USTACK_TOP in *.
    pose proof (munch_refl [(sp + -16, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. step.

    chk0 SHZS SV. step. if_false.
    astep. chk0 SHZS (SV + 8). step. if_false.
    step.
    name_mem m1.
    lazymatch goal with H : rw_cells bsegs m1 (sp + -16) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    step. if_cases KN; zify_cond KN.
    {
      astep. step. step. step. release_frame FR1 ST1 sp. step.
      replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      lazymatch goal with H : stk bsegs m1 _ sp |- _ => rename H into ST1' end.
      eapply evt_eq; [| eapply (XNPOS m1)]; [atp_st_eq| lia| exact MU| exact WM| exact MI1| exact ST1']. }

    step. astep. replace (0 + A) with A by lia. step. if_dead1 by N0.
    astep. astep.
    replace (0 <? A) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (A <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor].
    astep. step. if_false.
    astep. replace (n + - 0) with n by lia. step.
    eapply evt_eq; [| eapply (XCHR m1)]; [unfold e_memchr; atp_st_eq| lia| exact MU| exact WM| exact MI1| exact ST1| exact FR1].
  Qed.

  Lemma svfind_post : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (sp A r res RA : Z)
      (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells bsegs m (sp + -16) [C8 s0; C8 (wz RA)] -> stk bsegs m (ae_lo E) (sp + -16) -> mem_inv bsegs m -> ae_lo E + 16 <= sp ->
    0 < A < 2^47 -> ((r = 0 /\ res = 18446744073709551615) \/ (A <= r < 2^47 /\ res = r - A)) ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (xa1 : word), stk bsegs m (ae_lo E) sp ->
       K (MS (mkR (wz RA) (wz sp) gp (wz TPV) t0 t1 t2 s0 s1 (wz res) xa1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz RA) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb915c) (wz (sp + -16)) gp (wz TPV) t0 t1 t2 (wz A) s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0xb915c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros FR ST MI LO AR RES RA0 RA2 HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    destruct RES as [[-> ->]|[RR ->]].
    -
      astep. cbn [Z.ltb Z.compare Z.b2z]. astep. astep. astep. rewrite lor_ones64 by (apply Z.mod_pos_bound; lia).
      step. step. step. step. release_frame FR ST sp. step.
      replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      apply evt_done. apply HK. assumption.
    - astep. replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. astep. astep. astep. rewrite Z.lor_0_l.
      step. step. step. step. release_frame FR ST sp. step.
      replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      apply evt_done. apply HK. assumption.
  Qed.
End SvFind.
