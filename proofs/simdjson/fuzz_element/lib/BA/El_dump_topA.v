(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_activewA Atp_defsA Atp_kitA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Atp_activewA Atp_arrlA El_esc_ifaceA El_dump_kitA El_dump_body1A El_dump_body2A El_dump_loopA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma d_walk0 : forall (S1 lo OSP DOC : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo S1 -> lo <= S1 - 288 -> 0x6ca000 <= lo -> S1 < 2^63 -> S1 mod 32 = 0 -> 0 <= OSP < 2^64 -> 0 <= DOC < 2^64 ->
  client_consts m -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a1' a2' : word) (js : list (list byte)),
      ms = entry_st (wz 0xb7304) (wz (S1 - 288)) gp (wz TPV_A) t0 t1 t2 (wz S1) (wz (S1 - 288)) (wz 128) a1' a2' a3 a4 a5 a6 a7
                    s2 (wz OSP) (wz DOC) s5 s6 s7 s8 s9 (wz SHB) s11 t3 t4 t5 t6 F fc e_stack_malloc_1 m1
      /\ munch [(S1 - 288, S1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (S1 - 288)
      /\ rw_cells asegs m1 (S1 - 288) ([C8 (wz 0); CB 8 (nth 0 js []); CB 8 (nth 1 js []); CB 8 (nth 2 js []); CB 8 (nth 3 js []); CB 8 (nth 4 js []); CB 8 (nth 5 js []);
            CB 8 (nth 6 js []); CB 8 (nth 7 js []); CB 8 (nth 8 js []); CB 8 (nth 9 js []); CB 8 (nth 10 js []); CB 8 (nth 11 js []); CB 8 (nth 12 js []);
            CB 8 (nth 13 js []); CB 8 (nth 14 js []); CB 8 (nth 15 js []); CB 8 (nth 16 js []); CB 8 (nth 17 js []); CB 8 (nth 18 js []); CB 8 (nth 19 js []);
            CB 8 (nth 20 js []); CB 8 (nth 21 js [])] ++ fa_saved (wz EL_DUMPRET_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\ length js = 22%nat)
    (MS (mkR (wz EL_DUMPRET_A) (wz S1) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz DOC) (wz OSP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz EL_DUMP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH S32 OR DR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, EL_DUMP_A, EL_DUMPRET_A, e_stack_malloc_1, fa_saved.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(S1 - 288, S1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 288%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 288 _ [] (repeat 8%nat 36)) in FR; [| reflexivity].
  cbn [repeat mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 14 lstep. zstep. zstep.
  rewrite (land_m32 (S1 + -288)) by lia.
  replace (32 * ((S1 + -288) / 32)) with (S1 + -288) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
    change (c0 :: rest) with ((c0 :: firstn 22 rest) ++ skipn 22 rest) in FR end.
  cbn [firstn skipn] in FR. replace (S1 + -288) with (S1 - 288) in * by lia.
  apply evt_done.
  lazymatch type of FR with rw_cells _ _ _ ((_ :: CB 8 ?x0 :: CB 8 ?x1 :: CB 8 ?x2 :: CB 8 ?x3 :: CB 8 ?x4 :: CB 8 ?x5 :: CB 8 ?x6 :: CB 8 ?x7 :: CB 8 ?x8 :: CB 8 ?x9 :: CB 8 ?x10
                                 :: CB 8 ?x11 :: CB 8 ?x12 :: CB 8 ?x13 :: CB 8 ?x14 :: CB 8 ?x15 :: CB 8 ?x16 :: CB 8 ?x17 :: CB 8 ?x18 :: CB 8 ?x19 :: CB 8 ?x20 :: CB 8 ?x21 :: _) ++ _) =>
    exists m1; eexists _, _; exists [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21] end.
  cbn [nth]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| reflexivity].
Qed.

Lemma d_walk1 : forall (D : dctx) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 < d_f1 D -> d_f1 D + 128 <= dq D -> d_f1 D mod 8 = 0 -> 0 < dF D -> dF D + 1024 <= dq D ->
  shad (d_f1 D) + 16 <= dq D -> (d_f1 D + 128 <= shad (d_f1 D) \/ shad (d_f1 D) + 16 <= d_f1 D) ->
  rw_cells asegs m (dq D) (dfr0 D) -> wr_at asegs m (d_f1 D) 120 -> wr_at asegs m (shad (d_f1 D)) 16 ->
  (forall m', munch [(dq D + 136, dq D + 144); (dq D + 160, dq D + 168); (d_f1 D, d_f1 D + 24); (shad (d_f1 D), shad (d_f1 D) + 16)] m m' -> wmono asegs m m' -> shz m' (dDOC D) 16) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb7304) (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz 0) (wz 0x18f84) (wz 0xb7290) (wz (-14)) (wz (-8)) a5 a6 a7
                   (wz (d_f1 D)) s3 (wz (dDOC D)) s5 (wz (shad (dDOC D))) (wz (shad (d_f1 D))) s8 s9 (wz SHB) s11 t3 t4 t5 t6) F (wz 0xb73c4) fc None m1 (seg_rom asegs)
      /\ munch [(dq D + 136, dq D + 144); (dq D + 160, dq D + 168); (d_f1 D, d_f1 D + 24); (shad (d_f1 D), shad (d_f1 D) + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (dq D) (dfr1 D (J D 17))
      /\ rw_cells asegs m1 (d_f1 D) [C8 (wz 0x41b58ab3); C8 (wz 0x18f84); C8 (wz 0xb7290)] /\ rw_cells asegs m1 (shad (d_f1 D)) (map (fun z => C1 (Z_to_bv 8 z)) f1sh))
    (MS (mkR (wz 0xb7304) (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (d_f1 D)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 (wz (dDOC D)) s5 s6 s7 s8 s9 (wz SHB) s11 t3 t4 t5 t6)
        F (ret_pc (wz 0xb7304)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Q0 QH F0 FH F8 E0 EH SH1 SH2 FR WF1 WS1 SHZD MI.
  destruct D as [X E f1 L sp0 cr m0 gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 js]. cbn [d_X d_E d_f1 d_gp d_j d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11] in *.
  destruct X as [usp S1 Fr lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  unfold dfr0, dfr1, dsaves, J, fa_saved, f1sh, shad, SHB in *. cbn [d_j d_f1 d_X d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11 lf_usp lf_S1 lf_F lf_lo map app nth] in *.
  rewrite (ret_pc_even 0xb7304) by lia.
  set (q := S1 - 288) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl asegs m) as WM.
  assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  destruct (wr_at_rw_CB m f1 24 (wr_at_sub m f1 120 f1 24 WF1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & FH1).
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH1; [| reflexivity]. cbn [mk_CB_cells app] in FH1.
  destruct (wr_at_rw_CB m _ 16 WS1 ltac:(lia)) as (jsx & FS1).
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] (repeat 1%nat 16)) in FS1; [| reflexivity]. cbn [repeat mk_CB_cells app] in FS1.

  zstep. zstep. lstep. zstep. if_true.

  zstep. zstep. zstep. astep. zstep. zstep. zstep. zstep. zstep.

  lstep. lstep. lstep.

  zstep. zstep. do 4 ls. zstep. do 4 ls. astep. do 8 ls.

  zstep. shz_pose SHZD (Fr + 120). zstep. shz_norm. lstep. zstep. if_false.
  apply evt_done. exists m1. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]. split; [exact WM|]. split; [assumption|].
  split; [exact FR|]. split; [exact FH1| exact FS1].
Qed.

Lemma d_walk2 : forall (D : dctx) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok (d_E D) -> ae_DOC (d_E D) = dDOC D -> AINV_A (d_E D) m -> shz m (ae_TAPE (d_E D)) (8 * ae_n (d_E D)) -> mem_inv asegs m ->
  evt asegs (fun ms =>
      ms = MS (mkR (wz 0xb73e4) (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) (wz 0) a2 a3 a4 a5 a6 a7
                   (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (ae_T (d_E D) 0)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (d_s8 D) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
              F (wz EL_INS_UL) fc None m (seg_rom asegs))
    (MS (mkR x1 (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) s5 (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (d_s8 D) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
        F (wz 0xb73c4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros OK EDOC AI SHZT MI.
  destruct D as [X E f1 L sp0 cr m0 gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 js]. cbn [d_X d_E d_f1 d_gp d_j d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11] in *.
  destruct X as [usp S1 Fr lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR]. unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _). rewrite EDOC in DOCC.
  unfold shad, SHB in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 0 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_0_r, Z.add_0_r in RDT.

  step. chk0 SHZT (ae_TAPE E). step. if_false. step. step. step.
  apply evt_done. atp_st_eq_goal.
Qed.

Lemma d_walk3 : forall (D : dctx) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) (jc js : list byte) F fc (m : mem),
  0 < d_f1 D -> d_f1 D + 128 < 2^63 -> d_f1 D mod 8 = 0 -> shad (d_f1 D) + 16 < 2^63 -> (d_f1 D + 128 <= shad (d_f1 D) \/ shad (d_f1 D) + 16 <= d_f1 D) ->
  0 <= ae_T (d_E D) 0 < 2^64 ->
  rw_cells asegs m (d_f1 D + 112) [CB 1 jc] -> rw_cells asegs m (shad (d_f1 D) + 14) [CB 1 js] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb7410) (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) (wz (d_f1 D + 112)) (wz 1) a3 a4 a5 a6 a7
                   (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (ae_T (d_E D) 0)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (wz (ttype (ae_T (d_E D) 0))) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
              F (wz EL_OSPUT) fc None m1 (seg_rom asegs)
      /\ munch [(d_f1 D + 112, d_f1 D + 113); (shad (d_f1 D) + 14, shad (d_f1 D) + 15)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (d_f1 D + 112) [C1 (Z_to_bv 8 (ttype (ae_T (d_E D) 0)))] /\ rw_cells asegs m1 (shad (d_f1 D) + 14) [C1 (Z_to_bv 8 1)])
    (MS (mkR x1 (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) a1 a2 a3 a4 a5 a6 a7
             (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (ae_T (d_E D) 0)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) s8 (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
        F (ret_pc (wz 0xb73f4)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH F8 SHH SAP TR FC FS MI.
  destruct D as [X E f1 L sp0 cr m0 gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 jj]. cbn [d_X d_E d_f1 d_gp d_j d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11] in *.
  destruct X as [usp S1 Fr lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  unfold shad, SHB in *. rewrite (ret_pc_even 0xb73f4) by lia.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f1 / 8 + 2147450880 + 14) with (f1 / 8 + 2147450894) in FS by lia.
  zstep. astep. change (ae_T E 0 / 2 ^ 56) with (ttype (ae_T E 0)). zstep. ls. ls. zstep. zstep.
  apply evt_done. exists m2. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption|]. replace (f1 / 8 + 2147450880 + 14) with (f1 / 8 + 2147450894) by lia. split; [exact FC| exact FS].
Qed.

Lemma d_walk4 : forall (D : dctx) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (js : list byte) F fc (m : mem),
  0 < d_f1 D -> shad (d_f1 D) + 16 < 2^63 -> ttype (ae_T (d_E D) 0) = 114 ->
  rw_cells asegs m (shad (d_f1 D) + 14) [CB 1 js] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb7434) (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) (wz 0x23880) (wz 16) a3 a4 a5 a6 a7
                   (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (ae_T (d_E D) 0)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (wz 114) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
              F (wz EL_OSPUT) fc None m1 (seg_rom asegs)
      /\ munch [(shad (d_f1 D) + 14, shad (d_f1 D) + 15)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1)
    (MS (mkR x1 (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (ae_T (d_E D) 0)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (wz (ttype (ae_T (d_E D) 0))) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
        F (ret_pc (wz 0xb7410)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 SHH TY FS MI.
  destruct D as [X E f1 L sp0 cr m0 gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 jj]. cbn [d_X d_E d_f1 d_gp d_j d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11] in *.
  destruct X as [usp S1 Fr lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  unfold shad, SHB in *. rewrite (ret_pc_even 0xb7410) by lia. rewrite TY.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f1 / 8 + 2147450880 + 14) with (f1 / 8 + 2147450894) in FS by lia.
  zstep. zstep. ls. zstep. if_false. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM| assumption].
Qed.

Lemma d_walk5 : forall (D : dctx) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 <= ae_T (d_E D) 0 < 2^64 ->
  rw_cells asegs m (dq D) (dfr1 D (J D 17)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb744c) (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) (wz (tval (ae_T (d_E D) 0))) a2 a3 a4 a5 a6 a7
                   (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (tval (ae_T (d_E D) 0))) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (wz 114) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
              F (wz EL_INS_UL) fc None m1 (seg_rom asegs)
      /\ munch [(dq D + 144, dq D + 152)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 (dq D) (dfr1 D (C8 (wz MASK56))))
    (MS (mkR x1 (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) a1 a2 a3 a4 a5 a6 a7
             (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (ae_T (d_E D) 0)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (wz 114) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
        F (ret_pc (wz 0xb7434)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Q0 QH TR FR MI.
  destruct D as [X E f1 L sp0 cr m0 gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 jj]. cbn [d_X d_E d_f1 d_gp d_j d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11] in *.
  destruct X as [usp S1 Fr lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  unfold dfr1, dsaves, J, fa_saved, MASK56, shad, SHB in *. cbn [d_j d_f1 d_X d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11 lf_usp lf_S1 lf_F lf_lo app nth] in *.
  rewrite (ret_pc_even 0xb7434) by lia. set (q := S1 - 288) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl asegs m) as WM.
  assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  zstep. zstep. lstep. zstep. rewrite ?land64_mod, (land_mask56 (ae_T E 0)) by lia. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption| exact FR].
Qed.

Lemma d_walk6 : forall (D : dctx) (hm : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 < d_f1 D -> d_f1 D + 128 < 2^63 -> 0 < dF D -> dF D + 1024 < 2^63 -> 2 < hm < 2^32 ->
  rw_cells asegs m (dq D) (dfr1 D (C8 (wz MASK56))) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word),
      ms = MS (mkR x1 (wz (dq D)) (d_gp D) (wz TPV_A) t0' t1' t2 (wz (lf_S1 (d_X D))) (wz (dq D))
                   a0' a1' a2' a3' a4' a5' a6' a7'
                   (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (hm)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (wz 114) (d_s9 D) (wz SHB) (wz 1) t3 t4 t5 t6)
              F (wz 0xb7508) fc None m1 (seg_rom asegs)
      /\ munch [(dq D + 24, dq D + 136); (dq D + 152, dq D + 160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 (dq D) (dfrL D (nth 20 (d_j D) []) (nth 21 (d_j D) [])))
    (MS (mkR x1 (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) a1 a2 a3 a4 a5 a6 a7
             (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (hm)) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) (wz 114) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
        F (ret_pc (wz 0xb745c)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Q0 QH F0 FH E0 EH NR FR MI.
  destruct D as [X E f1 L sp0 cr m0 gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 jj]. cbn [d_X d_E d_f1 d_gp d_j d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11] in *.
  destruct X as [usp S1 Fr lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  unfold dfr1, dfrL, dsaves, J, fa_saved, MASK56, shad, SHB in *. cbn [d_j d_f1 d_X d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11 lf_usp lf_S1 lf_F lf_lo app nth] in *.
  rewrite (ret_pc_even 0xb745c) by lia. set (q := S1 - 288) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl asegs m) as WM.
  assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (wz (Fr + 120)) = Fr + 120) by (apply unsigned_lit; lia).
  assert (ED8 : bv_unsigned (wz (Fr + 128)) = Fr + 128) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (wz (hm)) = hm) by (apply unsigned_lit; lia).
  zstep. zstep. if_false.

  zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep.

  zstep. do 9 zstep.
  zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. lstep.
  astep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep. zstep.
  apply evt_done. do 11 eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption| exact FR].
Qed.

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold EL_DUMP_STACK_A, FUZZ_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma d_enter : forall (Σ : rts RT) (K : config -> Prop) (X : lfA) (E : aenvA) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> tape_wfS (ae_T E) (ae_S E) (ae_sn E) ck_any (ae_n E) ->
  a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m (lf_lo X) (lf_S1 X) -> lf_lo X + EL_DUMP_STACK_A <= lf_S1 X + 96 ->
  AINV_A E m -> el_libA m -> LOCBA m -> io_ssp m -> OSFRESHA m (lf_F X + 240) -> bytes_at asegs m (shad (lf_F X + 240)) (repeat z8 36) ->
  (forall (f1 : Z) (js : list (list byte)) (Σ1 : rts RT) (m2 : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word),
     let D := mkD X E f1 (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 js in
     dctx_ok D -> GINVA RT (d_G D) 0x1002 0 FILLOK (dfr0 D) 1 Σ1 m2 ->
     aevt RT PMc Σ1 K (MS (mkR (wz 0xb7304) (wz (dq D)) gp (wz TPV_A) t0' t1' t2' (wz (lf_S1 X)) (wz (dq D)) (wz f1) a1' a2' a3' a4' a5' a6' a7'
                              s2 (wz (dOS D + 128)) (wz (dDOC D)) s5 s6 s7 s8 s9 (wz SHB) s11 t3' t4' t5' t6')
                         F' (ret_pc (wz 0xb7304)) fc None m2 (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR (wz EL_DUMPRET_A) (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (ae_DOC E)) (wz (lf_F X + 240 + 128)) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz EL_DUMP_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LK OKE LE WFS AL FRS CR1 HA MI ST NEED AI LIB LB IOS OSF SHO HK.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp S1 Fv lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof (af_sp0_range RT AF Σ m HA) as SP0R. pose proof AL as (ALT & ALS & ALP & ALF & WLO).
  rewrite EDOC.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (d_walk0 S1 lo (Fv + 240 + 128) (Fv + 120) gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m);
    [exact ST| clear - NEED; ul| clear - LLO; ul| clear - SPT SPR; ul| exact SPA'| clear - FPOS FLO LOR SPT; ul| clear - FPOS FLO LOR SPT; ul
    | exact (af_client_consts RT AF Σ m HA)| exact MI]|].
  cbv beta. intros ms1 (m1 & a1' & a2' & js & -> & MU1 & WM1 & MI1 & ST1 & FR1 & LJ). apply evt_done. unfold entry_st.
  set (q := S1 - 288) in *.
  assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; clear - NEED LLO SPT SPR; ul).
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) S1 (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ m S1 _ HA Ha); clear - H NEED WLO ELO; ul. }

  eapply (aevt_smalloc1 RT PMc FDO MST RC2 Σ); [reflexivity| rewrite FRS; cbn [length]; unfold FRAMES_MAX2; lia| exact CR1| | exact MI1| | intros EF; rewrite FRS in EF; discriminate EF|].
  { apply (art_client_write RT AF Σ m m1 q HA ltac:(clear - NEED WLO ELO LLO; ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin SPT SPR; ul. }
  { unfold call_ok. rewrite EQ. split; [exact ST1|]. split; [clear - WLO ELO; lia|]. split; [clear - NEED; ul|]. split; [clear - SPT SPR; ul| clear - SPA'; subst q; Z.div_mod_to_equations; lia]. }
  intros Σ1 f1 w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 m2 (HA2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CRE F1P F164 F1T.
  rewrite EQ in ST2, PRES2. rewrite FRS in FRS1. change (fs_size 1) with 128 in WRF, WRS, F1T. change (128 / 8) with 16 in WRS. replace (128 - 8) with 120 in WRF by reflexivity.
  set (D := mkD (mkLF usp S1 Fv lo) E f1 (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 js).
  assert (GOK : gctx_ok (d_G D)).
  { subst D. apply (gctx_ok_intro RT AF _ Σ1 m2 HA2); cbn [d_G d_X d_E d_f1 d_L d_sp0 d_cr d_m0 lf_usp lf_S1 lf_F lf_lo g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0].
    - exact FRS1. - exact LV1. - exact SP1. - clear - SPA'; Z.div_mod_to_equations; lia. - lia. - clear - SPT SPR; ul. - clear - NEED; ul. - exact LLO. - rewrite <- ELO; exact WLO.
    - left; reflexivity. - right; reflexivity. }
  assert (GE : genv (d_G D) E).
  { subst D. unfold genv. cbn [d_G d_X d_E d_f1 d_L g_lo g_F g_L lf_lo lf_F]. split; [exact OKE|]. split; [exact ELO|]. split; [exact EDOC|]. split; [exact EFD|].
    split; [exact EKD|]. split; [exact ALT|]. split; [exact ALS|]. split; [exact ALP|]. rewrite EHI. cbn [d_G d_X g_q lf_S1]. clear - SPR. lia. }
  assert (DOK : dctx_ok D).
  { split; [exact GOK|]. split; [exact GE|]. split; [exact LK|]. split; [exact AI|]. split; [exact IOS|]. split; [exact WFS|]. split; [exact LJ| exact NEED]. }

  assert (REL2 : forall a : word, aclient (rt_live RT Σ) [(Fv, 4%nat)] (S1 - 288 + 288) (bv_unsigned a) -> outside (WD (Fv + 240)) (bv_unsigned a) -> m2 a = m a).
  { intros a Ha _. replace (S1 - 288 + 288) with S1 in Ha by lia. rewrite <- FRS in Ha.
    rewrite (PRES2 a); [exact (PRES1 a Ha)|]. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| clear; subst q; lia]. }
  assert (AGc : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x) -> agree_on P m m2).
  { intros P HP a Ha. pose proof (HP _ Ha) as CA. rewrite (PRES2 a); [exact (PRES1 a CA)|]. apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| auto| clear; subst q; lia]. }
  assert (INF : In (Fv, 4%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (CLF : forall x, Fv <= x < Fv + 1016 -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x).
  { intros x Hx. right; right; right; left. exists Fv, 4%nat. split; [exact INF| change (fs_size 4) with 1024; lia]. }
  assert (CLS : forall x, shad Fv <= x < shad Fv + 128 -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x).
  { intros x Hx. do 4 right. exists Fv, 4%nat. split; [exact INF| change (fs_size 4) with 1024; unfold shad in *; clear - Hx F64; Z.div_mod_to_equations; lia]. }
  assert (CLT : forall x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) S1 x) by (intros x Hx; right; left; exact Hx).
  apply (HK f1 js Σ1 m2 w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 DOK).
  split; [exact HA2|]. split; [exact MI2|].
  split; [subst D; cbn; exact FRS1|]. split; [subst D; cbn; exact LV1|]. split; [subst D; cbn; exact SP1|]. split; [subst D; cbn [d_G g_cr d_cr]; lia|].
  split; [subst D; cbn; exact ST2|].
  split. { exists 0xffffffff. split; [| left; reflexivity]. subst D. cbn [d_G g_F d_X lf_F].
           apply (proj1 (OSX_W m2 (Fv + 240) _)). apply (OSX_agree m m2 _ _ (OSFRESHA_OSX _ _ OSF)); [| exact (wmono_trans _ _ _ _ WM1 WM2)].
           apply AGc. intros x Hx. apply CLF. lia. }
  split. { subst D. cbn [d_G g_F d_X lf_F]. apply (bytes_at_agree asegs m m2 _ _ SHO). apply AGc. intros x Hx. rewrite repeat_length in Hx. apply CLS.
           unfold shad in *. clear - Hx F64. Z.div_mod_to_equations. lia. }
  split. { destruct LIB as [_ (_ & _ & TP)]. unfold el_tplocA, EL_TPLOC_A, EL_GLOC_A, TPV_A, LIBC_A in TP. unfold el_tploc.
           apply (rw_cells_agree_nw asegs m m2 _ _ TP). apply AGc. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply CLT. apply client_static_intro; clear - Hx; lia. }
  split. { apply (LOCBA_agree m m2 LB). apply AGc. intros x Hx. apply CLT. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. apply client_static_intro; clear - Hx; lia. }
  split. { split; [| subst D; reflexivity]. subst D. unfold dfr0, dsaves, J. cbn [d_X d_j d_f1 d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11 lf_usp lf_S1 lf_F lf_lo d_G g_q].
           apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros a Ha. apply PRES2. left. unfold fa_saved in Ha. cbn [cells_size csize Nat.add length app] in Ha.
           clear - Ha SPT SPR. ul. }
  split; [subst D; cbn; exact WRF|]. split; [subst D; cbn; exact WRS|].
  subst D. cbn [d_G g_L g_rfr g_q g_fsz g_m0 g_F d_X d_L d_m0 lf_S1 lf_F lf_usp]. exact REL2.
Qed.
End Top.

Section Top2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Variable D : dctx.
Hypothesis DOK : dctx_ok D.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis IUL : ins_ul_cpsA RT PMc.
Hypothesis CRB : EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n (d_E D) + EL_DUMP_CSB * ae_sn (d_E D) <= d_cr D.

Local Ltac ul := unfold EL_DUMP_STACK_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, FUZZ_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation GI := (GINVA RT (d_G D) 0x1002 0 FILLOK).

Local Ltac ownW A1 := intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia.
Notation n := (ae_n (d_E D)).

Lemma d_hdr : forall (Σ : rts RT) (K : config -> Prop) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  GI (dfr0 D) 1 Σ m -> frm0 fc -> KLOOPA RT PMc D K 1 0 ->
  aevt RT PMc Σ K (MS (mkR (wz 0xb7304) (wz (dq D)) (d_gp D) (wz TPV_A) t0 t1 t2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (d_f1 D)) a1 a2 a3 a4 a5 a6 a7
                          (d_s2 D) (wz (dOS D + 128)) (wz (dDOC D)) (d_s5 D) (d_s6 D) (d_s7 D) (d_s8 D) (d_s9 D) (wz SHB) (d_s11 D) t3 t4 t5 t6)
                     F (ret_pc (wz 0xb7304)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros GI0 FRM HK. replace (dOS D + 128) with (dF D + 368) by lia.
  pose proof DOK as (GOK & GE & LK & AI0 & IOS0 & WFS & LJ & _).
  pose proof GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL].
  cbn [d_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in *. change (fs_size 1) with 128 in *.
  pose proof GE as (OKE & ELOE & EDOC & EFD & EKD & INT & INS & INP & QHI). cbn [d_G g_lo g_F g_L] in ELOE, EDOC, EFD, INT, INS, INP.
  pose proof WFS as (NR & SNR & TR0 & _).
  assert (T0R : 0 <= ae_T (d_E D) 0 < 2^64) by (rewrite TR0; apply tword_range; unfold t_root; lia).
  assert (TY0 : ttype (ae_T (d_E D) 0) = 114) by (rewrite TR0, ttype_tword by lia; reflexivity).
  assert (TV0 : tval (ae_T (d_E D) 0) = n) by (rewrite TR0, tval_tword by lia; reflexivity).
  change (128 / 8) with 16 in *.
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 4) with 1024 in A1, A2, A3.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul).
  assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).

  apply (aevt_evt RT AF PMc MST).
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & WF1 & WS1 & _). cbn [d_G g_q g_ff g_FS g_ffk] in FR0, WF1, WS1. change (fs_size 1) with 128 in WF1, WS1.
  replace (128 - 8) with 120 in WF1 by reflexivity. change (128 / 8) with 16 in WS1.
  eapply evt_cut; [eapply (d_walk1 D t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 _ _ _ _ _ (d_s8 D) (d_s9 D) (d_s11 D) t3 t4 t5 t6 F fc m Q0 QH F0);
    [clear - FLO LQ; ul| exact F64x| exact E0| clear - ELO LQ; ul| clear - SHLO LQ; ul| exact SHAP| exact FR0| exact WF1| exact WS1| | exact MI0]|].
  { intros m' MU WM. rewrite <- EDOC. eapply (proj2 (proj2 (proj2 (proj2 (GINVA_wfacts RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI0 _ m' MU WM ltac:(ownW A1)))))). }
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FR1 & FH1 & FS1). apply evt_done.
  assert (GI1 : GI (dfr1 D (J D 17)) 1 Σ m1).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ (dfr0 D) _ 1 Σ m m1 _ GI0 MU1 WM1 MI1); [ownW A1| exact FR1| rewrite dfr1_size, dfr0_size; reflexivity]. }
  clear GI0 MI0 FR0 WF1 WS1 MU1 WM1 FR1 FH1 FS1.
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).

  pose proof (GINVA_wfacts RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI1 [] m1 (munch_refl [] m1) (wmono_refl asegs m1) ltac:(intros a; left; exact I)) as (_ & AI1 & SZT1 & _ & _).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (d_walk2 D); [exact OKE| exact EDOC| exact AI1| exact SZT1| exact MI1]|].
  cbv beta. intros ms2 ->. apply evt_done.
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_UL (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ 1 Σ K 0);
    [exact IUL| exact GI1| exact IOS0| intros f Hf; exact Hf| exact FA| clear; lia| exact FRM| apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' NR SNR; lia)|].
  clear m1 MI1 GI1 AI1 SZT1. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even 0xb73e4) by (clear; lia).
  cbn [d_G g_q g_F] in GI2 |- *.

  apply (aevt_evt RT AF PMc MST). zstep. zstep. zstep. zstep. apply evt_done.
  eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ 2 Σ2 K 0x23860 3 4 4%nat);
    [exact PUT| exact GI2| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity| clear; lia| clear; lia
    | clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' NR SNR; lia)|].
  clear m2 GI2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ3 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 m3 GI3. cbn [d_G g_q g_F] in GI3 |- *.

  pose proof GI3 as (_ & MI3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WF3 & WS3 & _). cbn [d_G g_ff g_FS g_ffk] in WF3, WS3. change (fs_size 1) with 128 in WF3, WS3.
  replace (128 - 8) with 120 in WF3 by reflexivity. change (128 / 8) with 16 in WS3.
  destruct (wr_at_cell m3 _ 120 112 1 WF3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jc FC3].
  destruct (wr_at_cell m3 _ 16 14 1 WS3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js FS3].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (d_walk3 D _ u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 _ u3 u4 u5 u6 jc js F3 fc2 m3 F0);
    [clear - FLO LQ QT; ul| exact F64x| clear - SHLO LQ QT; ul| exact SHAP| exact T0R| exact FC3| exact FS3| exact MI3]|].
  cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & FC4 & FS4). apply evt_done.
  assert (GI4 : GI (dfr1 D (J D 17)) 4 Σ3 m4).
  { pose proof GI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR3 & _) & _).
    eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ 4 Σ3 m3 m4 _ GI3 MU4 WM4 MI4); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw asegs m3 m4 _ _ FR3). apply (agree_of_munch _ _ _ _ MU4). intros x Hx. cbn [d_G g_q] in Hx. rewrite dfr1_size in Hx by reflexivity.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  clear GI3 MI3 WF3 WS3 FC3 FS3 MU4 WM4. rewrite TY0 in FC4.

  eapply (g_put_ownc RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ 4 Σ3 K 112 (Z_to_bv 8 114));
    [exact PUT| exact GI4| intros f Hf; exact Hf| exact FA| exact FC4| exact FS4| reflexivity| clear; lia| cbn [d_G g_ffk]; change (fs_size 1) with 128; clear; lia
    | apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' NR SNR; lia)|].
  clear MI4 GI4 FC4 FS4. intros Σ5 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F5 m5 GI5. cbn [d_G g_q g_F g_ff] in GI5 |- *.

  pose proof GI5 as (_ & MI5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR5 & _) & _ & WS5 & _). cbn [d_G g_ff g_FS g_ffk g_q] in WS5, FR5. change (fs_size 1) with 128 in WS5. change (128 / 8) with 16 in WS5.
  destruct (wr_at_cell m5 _ 16 14 1 WS5 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js5 FS5].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (d_walk4 D _ v0 v1 v2 _ c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 js5 F5 fc2 m5 F0); [clear - SHLO LQ QT; ul| exact TY0| exact FS5| exact MI5]|].
  cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6). apply evt_done.
  assert (GI6 : GI (dfr1 D (J D 17)) 6 Σ5 m6).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ 6 Σ5 m5 m6 _ GI5 MU6 WM6 MI6); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw asegs m5 m6 _ _ FR5). apply (agree_of_munch _ _ _ _ MU6). intros x Hx. cbn [d_G g_q] in Hx. rewrite dfr1_size in Hx by reflexivity.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  clear GI5 MI5 FR5 WS5 FS5 MU6 WM6.
  eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ 6 Σ5 K 0x23880 16 17 17%nat);
    [exact PUT| exact GI6| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity| clear; lia| clear; lia
    | clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' NR SNR; lia)|].
  clear m5 m6 MI6 GI6 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F5. intros Σ7 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F7 m7 GI7. cbn [d_G g_q g_F g_ff] in GI7 |- *.

  pose proof GI7 as (_ & MI7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR7 & _) & _). cbn [d_G g_q] in FR7.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (d_walk5 D _ v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F7 fc2 m7 Q0 QH T0R FR7 MI7)|].
  cbv beta. intros ms8 (m8 & -> & MU8 & WM8 & MI8 & FR8). apply evt_done.
  assert (GI8 : GI (dfr1 D (C8 (wz MASK56))) 8 Σ7 m8).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ 8 Σ7 m7 m8 _ GI7 MU8 WM8 MI8); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| exact FR8| rewrite !dfr1_size by reflexivity; reflexivity]. }
  clear GI7 MI7 FR7 MU8 WM8 FR8. rewrite TV0.
  eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_UL (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ 8 Σ7 K n);
    [exact IUL| exact GI8| exact IOS0| intros f Hf; exact Hf| exact FA| clear - NR; lia| exact FRM2| apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' NR SNR; lia)|].
  clear m7 m8 MI8 GI8 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F7. intros Σ9 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F9 fc9 m9 GI9 FRM9. cbn [d_G g_q g_F g_ff] in GI9 |- *.
  rewrite (ret_pc_even 0xb744c) by (clear; lia).

  apply (aevt_evt RT AF PMc MST). zstep. zstep. zstep. zstep. apply evt_done.
  eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ 9 Σ9 K 0x238c0 25 26 26%nat);
    [exact PUT| exact GI9| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity| clear; lia| clear; lia
    | clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' NR SNR; lia)|].
  clear m9 GI9 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F9. intros Σ11 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F11 m11 GI11. cbn [d_G g_q g_F g_ff] in GI11 |- *.

  pose proof GI11 as (_ & MI11 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR11 & _) & _). cbn [d_G g_q] in FR11.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (d_walk6 D n _ v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F11 fc9 m11 Q0 QH F0); [clear - FLO LQ QT; ul| exact E0| clear - ELO LQ QT; ul| exact NR| exact FR11| exact MI11]|].
  cbv beta. intros ms12 (m12 & t0' & t1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & -> & MU12 & WM12 & MI12 & FR12). apply evt_done.
  assert (GI12 : GI (dfrL D (nth 20 (d_j D) []) (nth 21 (d_j D) [])) 11 Σ11 m12).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ 11 Σ11 m11 m12 _ GI11 MU12 WM12 MI12); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| exact FR12| rewrite dfrL_size, dfr1_size by reflexivity; reflexivity]. }
  eapply (HK Σ11 m12 11 (nth 20 (d_j D) []) (nth 21 (d_j D) [])); [exact GI12| exact FRM9| clear; lia| unfold DKH; clear; lia].
Qed.
End Top2.

Lemma sj_lib_agree_d : forall m m', sj_lib m ->
  agree_on (fun x => 0x6a6340 <= x < 0x6a6348 \/ 0x6a6360 <= x < 0x6a6362 \/ 0x6a63e0 <= x < 0x6a640c \/ 0x6a6440 <= x < 0x6a6442) m m' -> sj_lib m'.
Proof.
  intros m m' [(A & B & C & D)|(A & B & C & D)] AG; [left| right]; unfold lib0, lib1 in *;
    (split; [| split; [| split]]; [eapply rw_cells_agree_nw; [exact A|] | eapply rw_cells_agree_nw; [exact B|] | eapply rw_cells_agree_nw; [exact C|] | eapply rw_cells_agree_nw; [exact D|]];
     intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia).
Qed.

Section Top3.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Variable D : dctx.
Hypothesis DOK : dctx_ok D.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis IUL : ins_ul_cpsA RT PMc.
Hypothesis CRB : EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n (d_E D) + EL_DUMP_CSB * ae_sn (d_E D) <= d_cr D.
Hypothesis LIB0 : el_libA (d_m0 D).

Local Ltac ul := unfold EL_DUMP_STACK_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, FUZZ_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation GI := (GINVA RT (d_G D) 0x1002 0 FILLOK).
Notation n := (ae_n (d_E D)).
Notation T := (ae_T (d_E D)).
Notation KLOOP := (KLOOPA RT PMc D).
Local Ltac facts DOK :=
  pose proof DOK as (GOK & GE & LK & AI0 & IOS0 & WFS & LJ & _);
  pose proof GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL];
  cbn [d_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in *; change (fs_size 1) with 128 in *; change (128 / 8) with 16 in *;
  pose proof GE as (OKE & ELOE & EDOC & EFD & EKD & INT & INS & INP & QHI); cbn [d_G g_lo g_F g_L] in ELOE, EDOC, EFD, INT, INS, INP;
  pose proof WFS as (NR & SNR & TR0 & _).

Definition dpostA (K : config -> Prop) : Prop :=
  forall (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (lf_lo (d_X D)) (lf_S1 (d_X D)) -> frm0 fc' ->
     rt_live RT Σ' = d_L D -> rt_frames RT Σ' = [(dF D, 4%nat)] -> rt_sp0 RT Σ' = d_sp0 D ->
     d_cr D - (EL_DUMP_C0 - 2 + EL_DUMP_CW * n + EL_DUMP_CSB * ae_sn (d_E D)) <= rt_credit RT Σ' ->
     rt_pres_fp (d_L D) [(dF D, 4%nat)] (lf_S1 (d_X D)) ([(dOS D, dOS D + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)] ++ EL_LIB_FP) (d_m0 D) m' ->
     AINV_A (d_E D) m' -> el_libA m' -> LOCBA m' -> OSDUMPA m' (dOS D) ->
     aevt RT PMc Σ' K (MS (mkR (wz EL_DUMPRET_A) (wz (lf_S1 (d_X D))) (d_gp D) (wz TPV_A) t0' t1' t2' (d_s0 D) (d_s1 D) a0' a1' a2' a3' a4' a5' a6' a7'
                       (d_s2 D) (d_s3 D) (d_s4 D) (d_s5 D) (d_s6 D) (d_s7 D) (d_s8 D) (d_s9 D) (d_s10 D) (d_s11 D) t3' t4' t5' t6')
                  F' (wz EL_DUMPRET_A) fc' None m' (seg_rom asegs)).

Lemma dump_exitA : forall (K : config -> Prop), dpostA K -> KLOOPA RT PMc D K (n - 1) (ae_sn (d_E D)).
Proof using AF FDO MST DOK PUT IUL CRB LIB0.
  intros K HK. unfold KLOOPA. intros Σ m k sv1 sv2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc GI0 FRM K0 KB. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 4) with 1024 in A1, A2, A3.
  pose proof WFS as (_ & _ & _ & TRN & _).
  assert (TR : 0 <= T (n - 1) < 2^64) by (rewrite TRN; apply tword_range; unfold t_root; clear; lia).
  assert (TY : ttype (T (n - 1)) = 114) by (rewrite TRN, ttype_tword by (clear; lia); reflexivity).
  eapply (dump_headA RT AF PMc FDO MST D DOK PUT IUL CRB K (n - 1)); [exact GI0| exact FRM| clear - NR; lia| exact TR| exact K0| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - KB NR SNR; lia|].
  intros Σ3 m3 x1' x5' x6' x7' x11' x12' x14' x15' x16' x17' x28' x29' x30' x31' F3 fc3 GI3 FRM3.
  pose proof GI3 as (HA3 & MI3 & FRS3 & LV3 & SP3 & CR3 & ST3 & _ & _ & _ & _ & (FR3 & _) & WF3 & WS3 & _).
  cbn [d_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in HA3, FRS3, LV3, SP3, CR3, ST3, FR3, WF3, WS3.
  change (fs_size 1) with 128 in WF3, WS3. replace (128 - 8) with 120 in WF3 by reflexivity. change (128 / 8) with 16 in WS3.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (x_w1 D (n - 1) x1' x5' x6' x7' x11' x12' x14' x15' x16' x17' x24 x28' x29' x30' x31' F3 fc3 m3 MI3 TY)|].
  cbv beta. intros ms1 (x11'' & x12'' & ->). apply evt_done.

  destruct (wr_at_cell m3 _ 120 0 8 WF3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jm FM3]. replace (d_f1 D + 0) with (d_f1 D) in FM3 by (clear; lia).
  destruct (wr_at_cell m3 _ 16 0 16 WS3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jsh FS3]. replace (shad (d_f1 D) + 0) with (shad (d_f1 D)) in FS3 by (clear; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (x_w2 D (n - 1) sv1 sv2 jm jsh x1' x5' x6' x7' x11'' x12'' x14' x15' x16' x17' x24 _ x28' x29' x30' x31' F3 fc3 m3 Q0 QH F0);
    [clear - FLO LQ QT; ul| clear - SHLO LQ QT; ul| exact SHAP| clear - FLO LQ; ul| clear - SHLO LQ; ul| exact FR3| exact FM3| exact FS3| exact MI3]|].
  cbv beta. intros ms2 (m4 & -> & MU4 & WM4 & MI4). apply evt_done.
  assert (GI4 : GI (dfrL D sv1 sv2) (k + 3) Σ3 m4).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ _ Σ3 m3 m4 _ GI3 MU4 WM4 MI4); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw asegs m3 m4 _ _ FR3). apply (agree_of_munch _ _ _ _ MU4). intros x Hx. cbn [d_G g_q] in Hx. rewrite dfrL_size in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  pose proof GI4 as (HA4 & _ & FRS4 & LV4 & SP4 & CR4 & ST4 & (fill4 & OX4 & FOK4) & SHO4 & TPL4 & LB4 & (FR4 & _) & _ & _ & REL4).
  cbn [d_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in HA4, FRS4, LV4, SP4, CR4, ST4, OX4, SHO4, FR4, REL4.
  pose proof (GINVA_ainv RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI4) as AI4.
  clear GI3 HA3 MI3 ST3 FR3 WF3 WS3 FM3 FS3 MU4 WM4 CR3 FRS3 LV3 SP3 m3.

  destruct (af_frame_release RT AF Σ3 m4 (d_f1 D) 1%nat [(dF D, 4%nat)] HA4 FRS4) as (Σ4 & fl & FLC & NAC & FL0 & FLW & FW & RELF).
  change (fs_size 1) with 128 in FW. replace (d_f1 D + 128 - 8) with (d_f1 D + 120) in FW by (clear; lia). rewrite SP4 in FLW.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (x_w3 D (n - 1) fl sv1 sv2 x1' x5' x6' x7' _ x14' x15' x16' x17' x24 _ x28' x29' x30' x31' F3 fc3 m4 Q0 QH FL0);
    [clear - FLW LO2 LQ QT; ul| clear - FLW LO2; lia| clear - LQ; ul| exact F0| clear - FLO LQ; ul| exact ST4| exact FR4| exact FLC| exact FW| exact MI4]|].
  cbv beta. intros ms3 (m5 & -> & MU5 & WM5 & MI5 & FL5 & ST5). apply evt_done.

  destruct (RELF m5 MU5 WM5 FL5) as (HA5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
  apply (aevt_switch RT PMc Σ3 Σ4 K _ AL5 AM5). rewrite (ret_pc_even EL_DUMPRET_A) by (clear; unfold EL_DUMPRET_A; lia).

  assert (NFL : forall x, aclient (d_L D) [(dF D, 4%nat)] (lf_S1 (d_X D)) x -> fl <= x < fl + 1 -> False).
  { intros x CA X. destruct CA as [SX|CA']; [clear - SX X FLW LO2 LQ; ul|].
    apply NAC. rewrite LV4, FRS4. replace fl with x by (clear - X; lia).
    apply (aclient_mono (d_L D) [(dF D, 4%nat)] USTACK_TOP); [right; exact CA'| auto| intros e He; right; exact He| clear; lia]. }

  assert (REL5 : forall a : word, aclient (d_L D) [(dF D, 4%nat)] (lf_S1 (d_X D)) (bv_unsigned a) -> outside (El_dump_kitA.WD (dOS D)) (bv_unsigned a) -> m5 a = d_m0 D a).
  { intros a CA OU. rewrite (MU5 a); [apply (REL4 a); [| exact OU]; apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| auto| clear; lia]|].
    cbn [outside]. split; [| exact I]. intros X. exact (NFL _ CA X). }
  eapply (HK Σ4 m5 fc3 F3); [exact HA5| exact MI5| exact ST5| exact FRM3| rewrite LV5; exact LV4| exact FRS5| rewrite SP5; exact SP4
    | rewrite CR5; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB, EL_DUMP_C0 in KB, CR4 |- *; clear - CR4 KB NR SNR; lia| | | | |].
  - intros a CA OU. apply REL5; [exact CA|]. clear - OU. unfold El_dump_kitA.WD. cbn [outside app] in OU |- *. tauto.
  - apply (AINV_A_agree (d_E D) m4 m5 AI4). apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [| exact I]. intros X.
    destruct (ainv_caller RT AF (d_G D) GOK (d_E D) x GE Hx) as [CA _]. cbn [d_G g_L g_rfr g_q g_fsz] in CA.
    apply (NFL x); [| exact X]. apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| auto| clear; lia].
  -
    destruct LIB0 as [(SJ0 & LOC0 & LW0) (EHG0 & UNW0 & TP0)].
    assert (AGS : forall P : Z -> Prop, (forall x, P x -> (0x6a6340 <= x < 0x6a6348 \/ 0x6a6360 <= x < 0x6a6362 \/ 0x6a63e0 <= x < 0x6a640c \/ 0x6a6440 <= x < 0x6a6442) \/ 0x6a6478 <= x < 0x6a7558 \/ 0x6a7d90 <= x < 0x6a7d98 \/ 0x6c81d8 <= x < 0x6c81dc) ->
              agree_on P (d_m0 D) m5).
    { intros P HP a Ha. pose proof (HP _ Ha) as R. apply REL5.
      - right; left. apply client_static_intro. clear - R. lia.
      - unfold El_dump_kitA.WD, EL_TPLOC_A, TPV_A. cbn [outside]. clear - R ESEG. unfold SEGTOP_A in ESEG. repeat split; try exact I; lia. }
    split; [split; [| split]| split; [| split]].
    + eapply sj_lib_agree_d; [exact SJ0|]. apply AGS. intros x Hx. left. exact Hx.
    + eapply pj_locA_agree; [exact LOC0|]. apply AGS. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. clear - Hx. lia.
    + eapply lockwA_agree; [exact LW0|]. apply AGS. intros x Hx. unfold PJ_LOCKW_A in Hx. clear - Hx. lia.
    + unfold el_ehgA in *. eapply rw_cells_agree_nw; [exact EHG0|]. apply AGS. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold EL_EHG_A in Hx. clear - Hx. lia.
    + destruct UNW0 as [uw U]. exists uw. eapply rw_cells_agree_nw; [exact U|]. apply AGS. intros x Hx. rewrite uw_cellsA_size in Hx. unfold EL_UNW_A in Hx. clear - Hx. lia.
    + change (el_tploc m5). eapply rw_cells_agree_nw; [exact TPL4|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      cbn [outside]. split; [| exact I]. intros X. apply (NFL x); [| exact X]. right; left. apply client_static_intro. clear - Hx. lia.
  - apply (LOCBA_agree m4 m5 LB4). apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [| exact I]. intros X. apply (NFL x); [| exact X].
    right; left. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. apply client_static_intro. clear - Hx. lia.
  - destruct (OSX_cellsA m5 (dOS D) fill4) as (pb & pp & ep & dum & j148 & j284 & H); [| exists pb, pp, ep, fill4, dum, j148, j284; exact H].
    apply (OSX_agree m4 m5); [apply (proj2 (OSX_W m4 (dOS D) fill4)); exact OX4| | exact WM5].
    apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [| exact I]. intros X. apply (NFL x); [| exact X].
    do 3 right; left. exists (dF D), 4%nat. split; [left; reflexivity| change (fs_size 4) with 1024; clear - Hx; lia].
Qed.
End Top3.

Section TopF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis IUL : ins_ul_cpsA RT PMc.
Hypothesis IU : ins_u_cpsA RT PMc.
Hypothesis IL : ins_l_cpsA RT PMc.
Hypothesis INSD : ins_d_cpsA RT PMc.
Hypothesis ESC : esc_cpsA RT PMc.

Theorem dump_okA : dump_cpsA RT PMc.
Proof.
  unfold dump_cpsA. intros Σ K X E OS t gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FDO MST LK OKE LE WFS EOS AL FRS CR HA MI ST NEED AI LIB LB NL IOS OSF SHO FRM HK.
  subst OS. pose proof WFS as (NR & SNR & _).
  eapply (d_enter RT AF RC2 PMc FDO MST Σ K X E); [exact LK| exact OKE| exact LE| exact WFS| exact AL| exact FRS
    | clear - CR NR SNR; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CR; lia| exact HA| exact MI| exact ST| exact NEED| exact AI| exact LIB| exact LB| exact IOS| exact OSF| exact SHO|].
  intros f1 js Σ1 m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' D DOK GI1.
  assert (CRB : EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n (d_E D) + EL_DUMP_CSB * ae_sn (d_E D) <= d_cr D) by exact CR.
  apply (d_hdr RT AF PMc FDO MST D DOK PUT IUL CRB Σ1 K); [exact GI1| exact FRM|].
  apply (dump_rootA RT AF RC RC2 PMc FDO MST D DOK PUT IUL IU IL INSD ESC CRB).
  apply (dump_exitA RT AF PMc FDO MST D DOK PUT IUL CRB LIB).
  unfold dpostA. intros Σ' m' fc' G' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HA' MI' ST' FRM' LV' FRS' SP' CR' PRES' AI' LIB' LB' OSD'.
  apply (HK Σ' m' fc' G'); [exact HA'| exact MI'| exact ST'| exact FRM'| exact LV'| rewrite FRS; exact FRS'| exact SP'| exact CR'| rewrite FRS; exact PRES'
    | exact AI'| exact LIB'| exact LB'| exact OSD'].
Qed.
End TopF.

Corollary dump_okA2 : forall RT, art_facts RT -> rt_contracts RT -> rt_contracts2 RT -> forall PMc,
  (fdfs_only PMc -> mat_stable PMc -> os_put_cpsA RT PMc) -> (fdfs_only PMc -> mat_stable PMc -> ins_ul_cpsA RT PMc) ->
  (fdfs_only PMc -> mat_stable PMc -> ins_u_cpsA RT PMc) -> (fdfs_only PMc -> mat_stable PMc -> ins_l_cpsA RT PMc) ->
  (fdfs_only PMc -> mat_stable PMc -> ins_d_cpsA RT PMc) -> (fdfs_only PMc -> mat_stable PMc -> esc_cpsA RT PMc) ->
  dump_cpsA RT PMc.
Proof.
  intros RT AF RC RC2 PMc P1 P2 P3 P4 P5 P6. intros Σ K X E OS t gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 sA sB sC sD. intros until m. intros FDO MST.
  exact (dump_okA RT AF RC RC2 PMc (P1 FDO MST) (P2 FDO MST) (P3 FDO MST) (P4 FDO MST) (P5 FDO MST) (P6 FDO MST) Σ K X E OS t gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 sA sB sC sD _ _ _ _ _ _ _ _ _ _ _ _ _ FDO MST).
Qed.
