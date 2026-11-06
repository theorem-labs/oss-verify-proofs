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
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA Atp_arratA El_sitesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
#[warnings="-notation-for-abbreviation"] Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition EL_ENDTHR_B : Z := 0xb8414.
Definition EL_ENDTHR_RET_B : Z := 0xb5594.
Definition EL_END_MSRET_B : Z := 0xb5584.

Definition h24_W (q : Z) : list ivl := [(q + -160, q)].

Definition end_frameB (j0 : list byte) (doc idx err : Z) (j28 : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0; C8 (wz doc); C8 (wz idx); C4 (wz err); CB 4 j28; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section H24.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma h24_walk1 : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (q node : Z),
    stk bsegs m (ae_lo E) q -> ae_lo E + 160 <= q -> SEGTOP_A <= ae_lo E -> q <= ae_hi E -> ae_hi E < 2^47 -> q mod 16 = 0 ->
    (forall m', munch (h24_W q) m m' -> wmono bsegs m m' -> shb_cells m') ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < node -> node + 16 <= q - 160 -> node mod 8 = 0 ->
    (forall m', munch (h24_W q) m m' -> wmono bsegs m m' -> shz m' node 16) -> AINV_A E m ->
    (forall m', munch (h24_W q) m m' -> AINV_A E m') ->
    (forall m', munch (h24_W q) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (h24_W q) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    mem_inv bsegs m ->
    evt bsegs (fun ms => exists (m0 : mem) (j0 j28 : list byte) (a3' a4' a5' t0' t1' t2' t3' t4' t5' t6' : word),
        munch (h24_W q) m m0 /\ wmono bsegs m m0 /\ mem_inv bsegs m0 /\ stk bsegs m0 (ae_lo E) (q + -80) /\
        ( (ttype (ae_T E 1) = 91 /\ rw_cells bsegs m0 (q + -80) (end_frameB j0 (ae_DOC E) 1 0 j28 s4 s3 s2 s1 s0 ra) /\
             ms = MS (mkR (wz EL_ENDTHR_RET_B) (wz (q + -80)) gp (wz TPV_A) t0' t1' t2' (wz node) (wz (node + 8)) (wz (q + -72)) (wz (ae_DOC E)) (wz 1) a3' a4' a5' a6 a7
                          (wz (shad node)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz EL_ENDTHR_B) fc None m0 (seg_rom bsegs))
       \/ (ttype (ae_T E 1) <> 91 /\ (exists j32, rw_cells bsegs m0 (q + -80) [CB 32 j32; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
             ms = MS (mkR (wz EL_END_MSRET_B) (wz (q + -80)) gp (wz TPV_A) t0' t1' t2' (wz node) (wz (node + 8)) (wz (q + -72)) (wz 0) (wz 16) a3' a4' a5' a6 a7
                          (wz (shad node)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz e_asan_memset) fc None m0 (seg_rom bsegs)) ))
      (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H24_A) fc None m (seg_rom bsegs)).
  Proof.
    intros until node. intros ST LO GLO QH HI47 Q16 SHBM NODE N0 NQ N8 SZN AI AIM SZD SZT MI.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP, EL_H24_A, SHB, h24_W in *.
    pose proof (ael_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q + -160, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.

    zstep. carve_frame 80%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    hide AI. do 6 lstep. unhide AI.

    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step. step.
    name_mem m1.
    assert (AI1 : AINV_A E m1) by exact (AIM m1 MU).
    pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY. rewrite Z.mul_1_r in RDTY.
    clear TAPEB AI1.

    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.

    astep. chk0 SZN (node + 8). step. if_false.
    step. zstep.

    assert (SUB : sub_fp [(q + -80 + -16, q + -80)] [(q + -160, q)]) by (intros x Hx; cbn [outside] in *; lia).
    eapply (tix_cps E OK _ m1 F fc (q + -80) 1 0xb5534);
      [exact (AIM m1 MU)| lia| exact (SHBM m1 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | exact ST| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2.
    assert (MU' : munch [(q + -160, q)] m m2) by exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU2)).
    assert (WM' : wmono bsegs m m2) by exact (wmono_trans _ _ _ _ WM WM2).
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells bsegs m2 (q + -80) cs);
      [eapply (rw_cells_agree bsegs m1 m2); [exact FR| | exact WM2]; apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia|] end.
    assert (NODE2 : rw_cells bsegs m2 node [C8 (wz (ae_DOC E)); C8 (wz 1)]).
    { eapply (rw_cells_agree bsegs m1 m2); [exact NODE| | exact WM2]. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. lia. }
    clear MU WM MU2 WM2 FR NODE. rename MU' into MU. rename WM' into WM. rename FR2 into FR. rename NODE2 into NODE.
    assert (AI2 : AINV_A E m2) by exact (AIM m2 MU).
    pose proof AI2 as (TAPEB & _ & _ & _ & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT2. rewrite Z.mul_1_r in RDT2.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY2. rewrite Z.mul_1_r in RDTY2.
    clear TAPEB AI2 RDT RDTY.
    replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep.
    destruct (Z.eq_dec (ttype (ae_T E 1)) 91) as [TY|TY].
    -
      rewrite TY. step. if_false.

      shz_pose SZN (node + 8). step. shz_norm. step. if_false.
      shz_pose SZN node. step. shz_norm. step. if_false.

      step. step. lstep. lstep. zstep. lstep. astep. zstep.
      apply evt_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?ja :: _ :: _ :: _ :: CB 4 ?jb :: _) => exists ja, jb end.
      do 10 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. left.
      split; [reflexivity|]. split; [exact FR|]. unfold EL_ENDTHR_RET_B, EL_ENDTHR_B, shad. atp_st_eq_goal.
    -
      step; if_cases KB; zify_cond KB; [| exfalso; rewrite ?land64_mod, ?Z.mod_small in KB by lia; lia].
      astep. step. step. zstep.
      apply evt_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
      exists [], []. do 10 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. right.
      split; [exact TY|]. split.
      { lazymatch type of FR with rw_cells _ ?mx _ (CB 8 ?ja :: CB 8 ?jb :: CB 8 ?jc :: CB 4 ?jd :: CB 4 ?je :: ?rest) =>
          pose proof (rw_cells_merge bsegs mx (q + -80) [] [CB 8 ja; CB 8 jb; CB 8 jc; CB 4 jd; CB 4 je] rest) as M;
          cbn [app cells_size csize Nat.add] in M; eexists; apply M; exact FR end. }
      unfold EL_END_MSRET_B, e_asan_memset, shad. atp_st_eq_goal.
  Qed.

  Lemma thr_walk_err : forall (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sv4 sv3 sv2 sv1 sv0 rae : word)
      (F : bvmap 5 word) (fc : bv 32) (mA m : mem) (q node : Z) (j24 j28 : list byte),
    munch (h24_W q) mA m -> wmono bsegs mA m ->
    stk bsegs m (ae_lo E) (q + -80) -> ae_lo E + 160 <= q -> SEGTOP_A <= ae_lo E -> q <= ae_hi E -> ae_hi E < 2^47 -> q mod 16 = 0 ->
    (forall m', munch (h24_W q) mA m' -> wmono bsegs mA m' -> shb_cells m') ->
    0 < node -> node + 16 <= q - 160 -> node mod 8 = 0 ->
    (forall m', munch (h24_W q) mA m' -> wmono bsegs mA m' -> shz m' (q + -72) 24) ->
    rw_cells bsegs m (q + -80) [CB 24 j24; C4 (wz 17); CB 4 j28; C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 rae] ->
    mem_inv bsegs m ->
    evt bsegs (fun ms => exists (m0 : mem) (j : list byte) (a0' a1' t0' t1' t2' t3' t4' t5' t6' : word),
        munch (h24_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ stk bsegs m0 (ae_lo E) (q + -144) /\
        rw_cells bsegs m0 (q + -80) [CB 24 j24; C4 (wz 17); CB 4 j28; C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 rae] /\
        rw_cells bsegs m0 (q + -144) [CB 8 j; C8 s5; C8 (wz (shad (node + 8))); C8 (wz SHB); C8 (wz (shad node)); C8 (wz (node + 8)); C8 (wz node); C8 (wz EL_ENDTHR_RET_B)] /\
        ms = MS (mkR (wz EL_ENDTHR_RET_B) (wz (q + -144)) gp (wz TPV_A) t0' t1' t2' (wz ((q + -56) / 8 + SHB)) (wz (q + -72)) a0' a1' a2 a3 a4 a5 a6 a7
                     (wz (q + -56)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (wz EL_SITE_END_B) fc None m0 (seg_rom bsegs))
      (MS (mkR (wz EL_ENDTHR_RET_B) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) (wz (node + 8)) (wz (q + -72)) a1 a2 a3 a4 a5 a6 a7
               (wz (shad node)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_ENDTHR_B) fc None m (seg_rom bsegs)).
  Proof.
    intros until j28. intros MU WM ST LO GLO QH HI47 Q16 SHBM N0 NQ N8 SZF FRE MI.
    unfold SEGTOP_A, USTACK_TOP, EL_ENDTHR_B, EL_ENDTHR_RET_B, EL_SITE_END_B, SHB, h24_W in *.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).

    zstep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 7 lstep.

    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step. step. astep.

    replace (q + -72 + 16) with (q + -56) by lia.
    chk0 SZF (q + -56). step. if_false.
    step. step. step. if_false. step. if_true.
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?ja :: _) => exists ja end.
    do 9 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FRE|]. split; [exact FR|].
    unfold shad. atp_st_eq_goal.
  Qed.

  Lemma thr_walk_arr : forall (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sv4 sv3 sv2 sv1 sv0 rae : word)
      (F : bvmap 5 word) (fc : bv 32) (mA m : mem) (q node : Z) (j0 j28 : list byte),
    munch (h24_W q) mA m -> wmono bsegs mA m ->
    stk bsegs m (ae_lo E) (q + -80) -> ae_lo E + 160 <= q -> SEGTOP_A <= ae_lo E -> q <= ae_hi E -> ae_hi E < 2^47 -> q mod 16 = 0 ->
    (forall m', munch (h24_W q) mA m' -> wmono bsegs mA m' -> shb_cells m') ->
    0 < node -> node + 16 <= q - 160 -> node mod 8 = 0 ->
    (forall m', munch (h24_W q) mA m' -> wmono bsegs mA m' -> shz m' (q + -72) 24) ->
    (forall m', munch (h24_W q) mA m' -> AINV_A E m') ->
    (forall m', munch (h24_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (h24_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    rw_cells bsegs m (q + -80) (end_frameB j0 (ae_DOC E) 1 0 j28 sv4 sv3 sv2 sv1 sv0 rae) ->
    ttype (ae_T E 1) = 91 -> mem_inv bsegs m ->
    evt bsegs (fun ms => exists (m0 : mem) (a1' a2' a3' a4' t0' t1' t2' t3' t4' t5' t6' : word),
        munch (h24_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ stk bsegs m0 (ae_lo E) (q + -80) /\
        rw_cells bsegs m0 (q + -80) (end_frameB j0 (ae_DOC E) 1 0 j28 sv4 sv3 sv2 sv1 sv0 rae) /\
        ms = MS (mkR (wz EL_ENDTHR_RET_B) (wz (q + -80)) gp (wz TPV_A) t0' t1' t2' (wz node) (wz (node + 8)) (wz (ae_DOC E)) a1' a2' a3' a4' a5 a6 a7
                     (wz (shad node)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (wz EL_ENDTHR_RET_B) fc None m0 (seg_rom bsegs))
      (MS (mkR (wz EL_ENDTHR_RET_B) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) (wz (node + 8)) (wz (q + -72)) a1 a2 a3 a4 a5 a6 a7
               (wz (shad node)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_ENDTHR_B) fc None m (seg_rom bsegs)).
  Proof.
    intros until j28. intros MU WM ST LO GLO QH HI47 Q16 SHBM N0 NQ N8 SZF AIM SZD SZT FRE TY MI.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP, EL_ENDTHR_B, EL_ENDTHR_RET_B, SHB, h24_W, end_frameB in *.
    pose proof (ael_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.
    assert (SUB : sub_fp [(q + -144 + -16, q + -144)] [(q + -160, q)]) by (intros x Hx; cbn [outside] in *; lia).

    zstep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 7 lstep.

    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step. step. astep.

    replace (q + -72 + 16) with (q + -56) by lia.
    chk0 SZF (q + -56). step. if_false.
    step. step. step. if_false. step. if_false.

    chk0 SZF (q + -72). step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. replace (q + -72 + 8) with (q + -64) by lia. chk0 SZF (q + -64). step. if_false.
    step. step. zstep.
    name_mem m1.
    eapply (tix_cps E OK _ m1 F fc (q + -144) 1 0xb84a8);
      [exact (AIM m1 MU)| lia| exact (SHBM m1 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2.
    assert (MU' : munch [(q + -160, q)] mA m2) by exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU2)).
    assert (WM' : wmono bsegs mA m2) by exact (wmono_trans _ _ _ _ WM WM2).
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR2 : rw_cells bsegs m2 (q + -144) cs);
      [eapply (rw_cells_agree bsegs m1 m2); [exact FR| | exact WM2]; apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia|] end.
    lazymatch type of FRE with rw_cells _ _ _ ?cs =>
      assert (FRE2 : rw_cells bsegs m2 (q + -80) cs);
      [eapply (rw_cells_agree bsegs m1 m2); [exact FRE| | exact WM2]; apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia|] end.
    clear MU WM MU2 WM2 FR FRE. rename MU' into MU. rename WM' into WM. rename FR2 into FR. rename FRE2 into FRE.
    assert (AI2 : AINV_A E m2) by exact (AIM m2 MU).
    pose proof AI2 as (TAPEB & _ & _ & _ & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT2. rewrite Z.mul_1_r in RDT2.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY2. rewrite Z.mul_1_r in RDTY2.
    clear TAPEB AI2.
    replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. rewrite TY. astep. step. step. if_false. astep. astep. astep. astep. step. if_true.

    astep. astep. astep. astep. astep. step. if_false.

    shz_pose SZF (q + -72). step. shz_norm. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    shz_pose SZF (q + -64). step. shz_norm. step. if_false.
    step. zstep.
    name_mem m3.
    eapply (tix_cps E OK _ m3 F fc (q + -144) 1 0xb8530);
      [exact (AIM m3 MU)| lia| exact (SHBM m3 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m4 ya1 ya3 ya4 MU4 WM4 MI4 ST4.
    assert (MU' : munch [(q + -160, q)] mA m4) by exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU4)).
    assert (WM' : wmono bsegs mA m4) by exact (wmono_trans _ _ _ _ WM WM4).
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (FR4 : rw_cells bsegs m4 (q + -144) cs);
      [eapply (rw_cells_agree bsegs m3 m4); [exact FR| | exact WM4]; apply (agree_of_munch _ _ _ _ MU4); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia|] end.
    lazymatch type of FRE with rw_cells _ _ _ ?cs =>
      assert (FRE4 : rw_cells bsegs m4 (q + -80) cs);
      [eapply (rw_cells_agree bsegs m3 m4); [exact FRE| | exact WM4]; apply (agree_of_munch _ _ _ _ MU4); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia|] end.
    clear MU WM MU4 WM4 FR FRE. rename MU' into MU. rename WM' into WM. rename FR4 into FR. rename FRE4 into FRE.
    assert (AI4 : AINV_A E m4) by exact (AIM m4 MU).
    pose proof AI4 as (TAPEB & _ & _ & _ & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT4. rewrite Z.mul_1_r in RDT4.
    pose proof (tape_read_lo32 E m4 1 TAPEB ltac:(lia)) as RDL4. rewrite Z.mul_1_r in RDL4.
    clear TAPEB AI4 RDT2 RDTY2.
    replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. zstep. astep. step.
    step. step. step. step. step. step. step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (STq : stk bsegs mx (ae_lo E) (q + -80))
        by (pose proof (stk_release bsegs mx (ae_lo E) _ _ ST4 FR ltac:(lia)) as X; cbn [cells_size csize Nat.add] in X; replace (q + -144 + Z.of_nat 64) with (q + -80) in X by lia; exact X) end.
    step. try rewrite (ret_pc_even 0xb5594) by lia.
    apply evt_done. exists m4. do 11 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact STq|]. split; [exact FRE|].
    replace (q + -144 + 64) with (q + -80) by lia. unfold shad. atp_st_eq_goal.
  Qed.

  Lemma h24_walk2 : forall (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sv4 sv3 sv2 sv1 sv0 rae : word)
      (F : bvmap 5 word) (fc : bv 32) (mA m : mem) (q node : Z) (j24 jd j28 : list byte),
    munch (h24_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> ae_lo E + 160 <= q -> SEGTOP_A <= ae_lo E -> q <= ae_hi E -> ae_hi E < 2^47 ->
    rw_cells bsegs m (q + -80) [CB 24 j24; CB 4 jd; CB 4 j28; C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 rae] -> mem_inv bsegs m ->
    evt bsegs (fun ms => exists (m0 : mem) (t0' t1' t2' t3' t4' t5' t6' : word),
        munch (h24_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ stk bsegs m0 (ae_lo E) (q + -80) /\
        rw_cells bsegs m0 (q + -80) [CB 24 j24; C4 (wz 17); CB 4 j28; C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0; C8 rae] /\
        ms = MS (mkR (wz EL_ENDTHR_RET_B) (wz (q + -80)) gp (wz TPV_A) t0' t1' t2' (wz node) (wz (node + 8)) (wz (q + -72)) a1 a2 a3 a4 a5 a6 a7
                     (wz (shad node)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (wz EL_ENDTHR_B) fc None m0 (seg_rom bsegs))
      (MS (mkR (wz EL_END_MSRET_B) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) (wz (node + 8)) (wz (q + -72)) a1 a2 a3 a4 a5 a6 a7
               (wz (shad node)) (wz SHB) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_END_MSRET_B) fc None m (seg_rom bsegs)).
  Proof.
    intros until j28. intros MU WM ST LO GLO QH HI47 FR MI.
    unfold SEGTOP_A, USTACK_TOP, EL_ENDTHR_B, EL_ENDTHR_RET_B, EL_END_MSRET_B, SHB, h24_W in *.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    step. lstep. astep. zstep.
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    do 7 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|].
    replace (q + -80 + 8) with (q + -72) by lia. unfold shad. atp_st_eq_goal.
  Qed.
End H24.

Section Arm24.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH in *; lia.

Lemma wf_len3 : forall (m : mem) A (ja jb jc jd : list byte) (na nb nc nd : nat) (rest : list cell),
  rw_cells bsegs m A (CB na ja :: CB nb jb :: CB nc jc :: CB nd jd :: rest) -> length ja = na /\ length jb = nb /\ length jc = nc /\ length jd = nd.
Proof. intros m A ja jb jc jd na nb nc nd rest [[WF _] _]. cbn [cells_wf cell_wf] in WF. tauto. Qed.
Lemma wf_len1 : forall (m : mem) A (ja : list byte) (na : nat) (rest : list cell),
  rw_cells bsegs m A (CB na ja :: rest) -> length ja = na.
Proof. intros m A ja na rest [[WF _] _]. cbn [cells_wf cell_wf] in WF. tauto. Qed.

Theorem arm24_okA : forall W, throw_siteB RT PMc W 24 EL_SITE_END_B -> arm_cpsA RT PMc W 24.
Proof using AF RC.
  intros W SITE Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED160 : lf_lo X + 16 <= lf_S1 X - 160) by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 24 sel idx jr jos t m 160 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED160) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof (arm_ctx_below RT AF X E Σ 24 sel idx jr jos t m) as CTX.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof AL as (ALT & ALS & ALP & ALF & WLO). rewrite ELO in WLO.
  change (el_arm_pcA 24) with 0xb246c. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO160 : f + 1024 <= sp' - 160) by (clear - FLO NEED160; lia).
  assert (COSTP : 0 <= arm_costA 24 (ae_n E) (ae_sn E) (zlength (ae_p1 E)))
    by (unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; pose proof (mcost_nonneg EXC_SIZE ltac:(unfold EXC_SIZE; lia)); lia).

  assert (SZFk : forall mx, ART RT Σ mx -> shz mx (sp' + -72) 24).
  { intros mx ARTx. apply (shz_stack RT AF Σ mx (sp' + -72) 24 ARTx); [clear - WLO NEED160; ul| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  assert (SZF : forall m', munch (h24_W sp') m m' -> wmono bsegs m m' -> shz m' (sp' + -72) 24) by (intros m' MU' WM'; exact (SZFk m' (ARTM m' MU' WM'))).
  apply (aevt_evt RT AF PMc MST).

  zstep. zstep.
  eapply evt_cut.
  { eapply (h24_walk1 E OKE (wz 0xb2474) gp t0 t1 t2 (wz usp) (wz sp') a1 a2 a3 a4 a5 a6 a7
              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3 t4 t5 t6 F fc m sp' (f + 208));
      [rewrite ELO; exact STg| rewrite ELO; clear - NEED160; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| exact SHBM| exact CE| clear - FPOS; lia| clear - FLO160; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SZN| exact AI| exact AIM| exact SZD| exact SZT| exact MIg]. }
  cbv beta. intros ms1 (m0 & j0 & j28 & a3' & a4' & a5' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & MU0 & WM0 & MI0 & ST0 & [(TY & FR0 & ->)|(TY & (j32 & FR0) & ->)]).
  -
    eapply evt_cut.
    { eapply (thr_walk_arr E OKE gp t0' t1' t2' (wz (ae_DOC E)) (wz 1) a3' a4' a5' a6 a7 (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3' t4' t5' t6'
                (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2474) F fc m m0 sp' (f + 208) j0 j28 MU0 WM0);
        [exact ST0| rewrite ELO; clear - NEED160; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia| exact SHBM| clear - FPOS; lia| clear - FLO160; lia| clear - F64; Z.div_mod_to_equations; lia
        | exact SZF| exact AIM| exact SZD| exact SZT| exact FR0| exact TY| exact MI0]. }
    cbv beta. intros ms2 (m5 & a1'' & a2'' & a3'' & a4'' & u0 & u1 & u2 & u3 & u4 & u5 & u6 & MU5 & WM5 & MI5 & ST5 & FRE5 & ->).
    unfold end_frameB, EL_ENDTHR_RET_B in *. rewrite ELO in ST5.
    assert (EQ5 : bv_unsigned (Z_to_bv 64 (sp' + -80)) = sp' + -80) by (apply unsigned_lit; clear - SPR SPT LLO LOR NEED160; ul).

    step. step. step. step. step. step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (STq : stk bsegs mx lo sp')
        by (pose proof (stk_release bsegs mx lo _ _ ST5 FRE5 ltac:(lia)) as X; cbn [cells_size csize Nat.add] in X; replace (sp' + -80 + Z.of_nat 80) with sp' in X by lia; exact X) end.
    step. try rewrite (ret_pc_even 0xb2474) by lia. zstep.
    apply evt_done. replace (sp' + -80 + 80) with sp' by lia.
    apply (POST false (rt_credit RT Σ) Σ m5 fc F).
    exact (arm_post_below_le RT AF W 24 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m5 fc 160 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED160
             MU5 WM5 MI5 STq FRM COSTP).
  -
    rewrite ELO in ST0.
    destruct (CTX m0 160 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED160 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    apply (rw_cells_split_CB bsegs _ _ [] 32 j32 _ [8; 16; 4; 4]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    pose proof (wf_len3 _ _ _ _ _ _ _ _ _ _ _ FR0) as (LJa & LJb & LJc & LJd).
    set (ja := firstn 8 j32) in *. set (jb := firstn 16 (skipn 8 j32)) in *. set (jc := firstn 4 (skipn 16 (skipn 8 j32))) in *.
    set (jd := firstn 4 (skipn 4 (skipn 16 (skipn 8 j32)))) in *. clearbody ja jb jc jd.
    apply evt_done.
    assert (EQ0 : bv_unsigned (Z_to_bv 64 (sp' + -80)) = sp' + -80) by (apply unsigned_lit; clear - SPR SPT LLO LOR NEED160; ul).
    assert (CD : checked_dst RT Σ m0 (wz (sp' + -80)) (sp' + -72) 16).
    { unfold checked_dst. rewrite EQ0. split; [| split].
      - intros _. split; [apply (af_acc_stack RT AF Σ m0 _ _ ART0); clear - WLO NEED160 SPT SPR; ul| right; right; left; clear - WLO NEED160 SPT SPR; ul].
      - intros i Hi. left. clear - Hi SPT SPR. ul.
      - apply (wr_at_sub m0 (sp' + -80) 80); [eapply rw_cells_wr_at; [exact FR0| cbn [cells_size csize Nat.add]; lia]| lia| lia| lia]. }
    assert (COK : call_ok RT Σ m0 (wz (sp' + -80)) lo).
    { unfold call_ok. rewrite EQ0. split; [exact ST0|]. split; [exact WLO|]. split; [clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul|].
      split; [clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia]. }
    eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 (sp' + -72) 16 z8 lo eq_refl eq_refl eq_refl
              ltac:(clear - SPT SPR LLO LOR NEED160; ul) ltac:(lia) CD ART0 MI0 COK).
    intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m6 (ART6 & MI6 & WM6 & ST6) PRES6 BY6. rewrite EQ0 in ST6, PRES6.
    rewrite (ret_pc_even 0xb5584) by lia. change (Z.to_nat 16) with 16%nat in BY6.

    assert (AG6 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) -> agree_on P m0 m6).
    { intros P HP. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES6). intros x Px. pose proof (HP x Px) as Hx. split.
      - destruct Hx as [H|H]; [left; clear - H; lia| right; exact H].
      - pose proof (NBELOW x Hx). clear - H. lia. }
    destruct (arm_mem_agree RT AF (mkLF usp sp' f lo) E Σ 24 sel idx jr jos t m0 m6 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART6 AM0 XD0 AUX0 AG6)
      as (AM6 & XD6 & AUX6). cbn [lf_usp lf_S1 lf_F lf_lo] in AM6, AUX6.

    assert (FR6 : rw_cells bsegs m6 (sp' + -80) [CB 24 (ja ++ repeat z8 16); CB 4 jc; CB 4 jd; C8 (wz (f + 32)); C8 (wz (shad f)); C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb2474)]).
    { pose proof (cells_mid_update m0 m6 (sp' + -80) [CB 8 ja] 16 jb (repeat z8 16) [CB 4 jc; CB 4 jd; C8 (wz (f + 32)); C8 (wz (shad f)); C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb2474)] FR0) as U.
      cbn [app cells_size csize Nat.add] in U.
      specialize (U ltac:(apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES6); intros x (Hx & Hn); split; [left; clear - Hx SPT SPR; ul| clear - Hn; lia])
                    WM6 ltac:(replace (sp' + -80 + 8) with (sp' + -72) by lia; exact BY6) ltac:(rewrite repeat_length; reflexivity)).
      pose proof (rw_cells_merge bsegs m6 (sp' + -80) [] [CB 8 ja; CB 16 (repeat z8 16)] [CB 4 jc; CB 4 jd; C8 (wz (f + 32)); C8 (wz (shad f)); C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb2474)] U) as M.
      cbn [app cells_size csize Nat.add cells_bytes cbytes] in M. rewrite app_nil_r in M. exact M. }

    pose proof (arm_entry_kit RT AF (mkLF usp sp' f lo) E Σ 24 sel idx jr jos t m6 160 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART6 AM6 ltac:(lia) NEED160)
      as (ARTM6 & SZN6 & AIM6 & SZD6 & SZT6 & SHBM6). cbn [lf_usp lf_S1 lf_F lf_lo] in ARTM6, SZN6, AIM6, SZD6, SZT6, SHBM6.
    assert (SZF6 : forall m', munch (h24_W sp') m6 m' -> wmono bsegs m6 m' -> shz m' (sp' + -72) 24) by (intros m' MU' WM'; exact (SZFk m' (ARTM6 m' MU' WM'))).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { eapply (h24_walk2 E gp w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) w3 w4 w5 w6
                (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2474) F2 fc m6 m6 sp' (f + 208) (ja ++ repeat z8 16) jc jd (munch_refl _ m6) (wmono_refl bsegs m6) ltac:(rewrite ELO; exact ST6));
        [rewrite ELO; clear - NEED160; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul| exact FR6| exact MI6]. }
    cbv beta. intros ms3 (m7 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & MU7 & WM7 & MI7 & ST7 & FR7 & ->).
    eapply evt_cut.
    { eapply (thr_walk_err E gp v0 v1 v2 g1 g2 g3 g4 g5 g6 g7 (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) v3 v4 v5 v6
                (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2474) F2 fc m6 m7 sp' (f + 208) (ja ++ repeat z8 16) jd MU7 WM7 ST7);
        [rewrite ELO; clear - NEED160; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia| exact SHBM6| clear - FPOS; lia| clear - FLO160; lia| clear - F64; Z.div_mod_to_equations; lia
        | exact SZF6| exact FR7| exact MI7]. }
    cbv beta. intros ms4 (m8 & jt & a0' & a1' & x0 & x1 & x2 & x3 & x4 & x5 & x6 & MU8 & WM8 & MI8 & ST8 & FRE8 & FRT8 & ->).

    destruct (arm_ctx_below RT AF (mkLF usp sp' f lo) E Σ 24 sel idx jr jos t m6 m8 160 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART6 AM6 ltac:(lia) NEED160 XD6 AUX6 MU8 WM8)
      as (ART8 & AM8 & XD8 & AUX8 & NBELOW8 & AGM8). cbn [lf_usp lf_S1 lf_F lf_lo] in AM8, AUX8, NBELOW8, AGM8.
    rewrite ELO in ST8.
    pose proof (wf_len1 _ _ _ _ _ FRT8) as LJt. pose proof (wf_len1 _ _ _ _ _ FRE8) as LJ24.
    unfold EL_ENDTHR_RET_B in FRT8, FRE8.
    assert (FRS8 : rw_cells bsegs m8 (sp' - site_fszB EL_SITE_END_B) (site_frameB EL_SITE_END_B (mkLF usp sp' f lo) (jt ++ (ja ++ repeat z8 16) ++ jd) 17)).
    { rewrite (site_frame_endB_intro (mkLF usp sp' f lo) jt (ja ++ repeat z8 16) jd 17 LJt LJ24). cbn [lf_usp lf_S1 lf_F lf_lo lftoi_savedB site_fszB EL_SITE_END_B Z.eqb Pos.eqb].
      replace (sp' - 144) with (sp' + -144) by lia.
      apply (proj2 (rw_cells_app bsegs m8 (sp' + -144) [CB 8 jt; C8 (wz (f + 96)); C8 (wz (shad (f + 216))); C8 (wz SHB); C8 (wz (shad (f + 208))); C8 (wz (f + 216)); C8 (wz (f + 208)); C8 (wz 0xb5594)] _)).
      split; [replace (f + 216) with (f + 208 + 8) by lia; exact FRT8|]. cbn [cells_size csize Nat.add]. replace (sp' + -144 + Z.of_nat 64) with (sp' + -80) by lia. exact FRE8. }
    apply evt_done. replace (sp' + -144) with (sp' - site_fszB EL_SITE_END_B) by reflexivity.
    eapply (SITE Σ K {| lf_usp := usp; lf_S1 := sp'; lf_F := f; lf_lo := lo |} E sel idx jr jos t (jt ++ (ja ++ repeat z8 16) ++ jd) 17
              (wz 0xb5594) gp x0 x1 x2 (wz ((sp' + -56) / 8 + SHB)) (wz (sp' + -72)) a0' a1' g2 g3 g4 g5 g6 g7 (wz (sp' + -56)) (wz SHB) (wz (shad (f + 208 + 8)))
              s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) x3 x4 x5 x6 F2 fc m8);
      cbn [lf_usp lf_S1 lf_F lf_lo site_fszB site_jlenB site_cvB site_regsB el_site_pcsB EL_SITE_END_B EL_SITE_CSTR_B EL_SITE_SV_B Z.eqb Pos.eqb orb andb app];
      [left; reflexivity| exact FDO| exact MST| exact LK| exact OKE| exact LE| exact SEL| exact IDX| exact AL| exact FRS| exact LPA
      | clear - LVB; unfold arm_xliveA in LVB; cbn [Z.eqb Pos.eqb orb] in LVB; lia
      | clear - CRB; unfold arm_costA in CRB; cbn [Z.eqb Pos.eqb orb] in CRB; lia
      | exact ART8| exact MI8| replace (sp' - 144) with (sp' + -144) by lia; exact ST8
      | clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; lia
      | exact AM8| exact FRM| exact XD8| exact AUX8| exact SPB
      | rewrite !length_app, repeat_length, LJt, LJa, LJd; reflexivity| lia
      | exact FRS8| replace (sp' - 144 + 88) with (sp' + -56) by lia; repeat split; reflexivity|].
    intros c Σ' m' fc' F' ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6' a7' s6' s7' s8' s9' s10' s11' t3'' t4'' t5'' t6'' LP.
    unfold lf_st, EL_LRET_A. cbn [lf_usp lf_S1 lf_F lf_lo].
    destruct LP as (AX & MI' & ST' & FRM' & LV' & FRS' & SP' & CR' & PRES' & MEM' & _). cbn [lf_usp lf_S1 lf_F lf_lo] in ST', PRES', MEM'.
    apply (aevt_evt RT AF PMc MST). zstep. apply evt_done.
    apply (POST true c Σ' m' fc' F'). unfold arm_postA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [exact AX|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|]. split; [exact LV'|]. split; [exact FRS'|]. split; [exact SP'|].
    split; [exact CR'|].
    split.
    {
      intros a Ha Ho. rewrite (PRES' a Ha Ho). rewrite (MU8 a); [| cbn [outside]; split; [exact (NBELOW8 _ Ha)| exact I]].
      rewrite (PRES6 a); [| destruct Ha as [H|H]; [left; clear - H; lia| right; exact H]| pose proof (NBELOW _ Ha); clear - H; lia].
      apply MU0. cbn [outside]. split; [exact (NBELOW _ Ha)| exact I]. }
    split; [exact MEM'| intros _; right; lia].
Qed.
End Arm24.
