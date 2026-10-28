(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit X_ixdefs Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit4A Atp_fzwA Atp_activewA Atp_pidwA Pj_rtkA Pj_cpsA Pj_defsA Atp_hkit5A Imp_hdefs0A Imp_libifaceA Imp_gsidefsA Imp_annotA Imp_gsi1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Lemma b2z_pos : forall x, 0 < x -> Z.b2z (0 <? x) = 1.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, 0 < x -> Z.b2z (x <? 1) = 0.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Local Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Definition pb_statsh (m : mem) : Prop :=
  ro_cells bsegs m 0x800cf800 [C1 z8] /\ ro_cells bsegs m 0x800cf801 [C1 z8] /\ ro_cells bsegs m 0x800cf802 [C1 z8] /\ ro_cells bsegs m 0x800cf834 [C1 z8].

Definition pb_stksh (usp : Z) (m : mem) : Prop :=
  ro_cells bsegs m (usp / 8 + 2147450869) [C1 z8] /\ ro_cells bsegs m (usp / 8 + 2147450870) [C1 z8]
  /\ ro_cells bsegs m (usp / 8 + 2147450871) [C1 z8] /\ ro_cells bsegs m (usp / 8 + 2147450872) [C1 z8] /\ ro_cells bsegs m (usp / 8 + 2147450873) [C1 z8].

Lemma pb_walk1 : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 176 -> 0x100000000 <= lo -> usp < 2^63 -> usp mod 16 = 0 ->
  client_consts m -> pb_statsh m -> pb_stksh usp m ->
  rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (j0 j1 : list byte),
      ms = MS (mkR (wz 0xbf3e0) (wz (usp - 160)) gp tp t0 t1 t2 (wz (usp - 64)) (wz 1) (wz 8) (wz 1) (wz 0x189978) (wz IMP_VEC_OBJ_A) (wz 0) a5 a6 a7
                   (wz (usp - 88)) (wz 0) (wz (usp / 8 + 2147450872)) (wz SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz OPNEW_A) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 176, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp - 160)
      /\ rw_cells bsegs m' (usp - 160) [CB 8 j1; C8 s5; C8 (wz SHB); C8 (wz 2148333569); C8 (wz IMP_AVP_ARR_A); C8 (wz IMP_VEC_OBJ_A)]
      /\ rw_cells bsegs m' (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf0f0)]
      /\ rw_cells bsegs m' (usp - 96) [CB 32 j0; C8 (wz 0); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz IMP_VEC_OBJ_A) (wz IMP_AVP_ARR_A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xbf038 m).
Proof.
  intros until m. intros ST LO GLO SPH U16 (CC1 & CC2 & _ & _) (SA8 & SA9 & SAA & SDC) (SK1 & SK2 & SK3 & SK4 & SK5) VEC MI.
  unfold entry_st, IMP_VEC_OBJ_A, IMP_AVP_ARR_A, OPNEW_A, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl [(usp - 176, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 96%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. if_true. zstep. zstep. zstep.
  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app] in FR1.
  ls. ls. ls. ls. ls. ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-64) ) / 8 + 2147450880) with ( usp / 8 + 2147450872 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. ls. zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-56) ) / 8 + 2147450880) with ( usp / 8 + 2147450873 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  ls. zstep. if_false. zstep. zstep. zstep. zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR2; [| reflexivity]. cbn [mk_CB_cells app] in FR2.
  ls. zstep. zstep. if_false. zstep. zstep. zstep. zstep.
  release_frame FR2 ST (usp + -160).
  replace (usp + -160) with (usp - 160) in * by lia. replace (usp + -112) with (usp - 112) in * by lia. replace (usp + -96) with (usp - 96) in * by lia.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR1|]. split; [exact FR0| exact FR].
Qed.

Lemma pb_walk2 : forall (usp lo A8 : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j0 j1 jc : list byte) F fc (m : mem),
  stk bsegs m lo (usp - 160) -> lo <= usp - 208 -> 0x100000000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 < A8 -> A8 + 8 < usp - 208 -> A8 mod 16 = 0 ->
  (A8 + 8 <= 0x10000 \/ 0x6e0000 <= A8) -> (A8 + 8 <= 0x7fff8000 \/ 0x10007fff7fff < A8) -> usp / 8 + 2147451000 <= lo -> A8 / 8 + 2147451000 <= lo ->
  (A8 + 8 <= usp / 8 + 2147450860 \/ usp / 8 + 2147450880 <= A8) ->
  client_consts m -> pb_statsh m -> pb_stksh usp m ->
  rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> ro_cells bsegs m IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)] ->
  rw_cells bsegs m A8 [CB 8 jc] -> ro_cells bsegs m (A8 / 8 + 2147450880) [C1 z8] ->
  rw_cells bsegs m (usp - 160) [CB 8 j1; C8 s5; C8 (wz SHB); C8 (wz 2148333569); C8 (wz IMP_AVP_ARR_A); C8 (wz IMP_VEC_OBJ_A)] ->
  rw_cells bsegs m (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf0f0)] ->
  rw_cells bsegs m (usp - 96) [CB 32 j0; C8 (wz 0); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a3' a4' a5' a6' : word) (j2 : list byte),
      ms = MS (mkR (wz 0xbf5bc) (wz (usp - 176)) gp tp t0 t1 t2 (wz (usp - 88)) (wz IMP_VEC_OBJ_A) (wz A8) (wz 0) (wz 0) a3' a4' a5' a6' a7
                   (wz (IMP_VEC_OBJ_A + 8)) (wz (usp - 80)) (wz A8) (wz SHB) (wz 2148333569) (wz (usp / 8 + 2147450870)) (wz 2148333568) s9 s10 s11 t3 t4 t5 t6) F (wz e_asan_memcpy) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 208, usp); (A8, A8 + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp - 176)
      /\ rw_cells bsegs m' A8 [C8 (wz SJ_SINGLETON)]
      /\ rw_cells bsegs m' (usp - 176) [C8 s8; C8 s7]
      /\ rw_cells bsegs m' (usp - 160) [C8 s6; C8 s5; C8 (wz SHB); C8 (wz 2148333569); C8 (wz IMP_AVP_ARR_A); C8 (wz IMP_VEC_OBJ_A)]
      /\ rw_cells bsegs m' (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf148)]
      /\ rw_cells bsegs m' (usp - 96) [CB 8 j2; C8 (wz A8); C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8)); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR (wz 0xbf3e0) (wz (usp - 160)) gp tp t0 t1 t2 (wz (usp - 64)) (wz 1) (wz A8) a1 a2 a3 a4 a5 a6 a7
             (wz (usp - 88)) (wz 0) (wz (usp / 8 + 2147450872)) (wz SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0xbf3e0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH U16 A80 A8H A16 A8SG ALV USH ASH ASK (CC1 & CC2 & _ & _) (SA8 & SA9 & SAA & SDC) (SK1 & SK2 & SK3 & SK4 & SK5) VEC ARR CH CS F1 F1b F0 MI.
  unfold IMP_VEC_OBJ_A, IMP_AVP_ARR_A, SJ_SINGLETON, e_asan_memcpy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl [(usp - 208, usp); (A8, A8 + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A8) = A8) by (apply unsigned_lit; lia).
  assert (AL7 : Z.land A8 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
  replace (usp - 160) with (usp + -160) in * by lia. replace (usp - 112) with (usp + -112) in * by lia. replace (usp - 96) with (usp + -96) in * by lia.
  replace (usp - 64) with (usp + -64) in * by lia. replace (usp - 88) with (usp + -88) in * by lia.
  apply (rw_cells_split_CB bsegs _ _ [] 32 j0 _ [8; 8; 8; 8]%nat) in F0; [| reflexivity]. cbn [mk_CB_cells app] in F0.
  repeat match type of F0 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in F0; clearbody j end.
  zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-88) ) / 8 + 2147450880) with ( usp / 8 + 2147450869 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. try replace (0 + A8 ) with A8 by lia. zstep. zstep. zstep. zstep. unz. if_false.
  zstep. zstep. zstep. zstep. zstep. if_false. zstep. if_false.
  zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-72) ) / 8 + 2147450880) with ( usp / 8 + 2147450871 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-80) ) / 8 + 2147450880) with ( usp / 8 + 2147450870 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. unz. if_false. zstep. zstep. zstep. if_false.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
  zstep. zstep. if_false. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. rewrite ?AL7. zstep. if_false. zstep. zstep. zstep. zstep. if_false.
  zstep. try rewrite shr3_div. zstep. zstep. zstep. if_false.
  zstep. ls. zstep. if_false. zstep. zstep. if_false. zstep. zstep. zstep. zstep. zstep. zstep. ls. ls. ls. ls. ls. ls. zstep. zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. if_false. zstep. zstep. zstep. if_false. zstep. zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app] in FR1.
  ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. if_false. zstep. if_true. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-80) ) / 8 + 2147450880) with ( usp / 8 + 2147450870 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. try replace ( A8 - 0) with A8 by lia. zstep. zstep. zstep. unz. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. zstep.
  try replace (0 + 9223372036854775808 ) with 9223372036854775808 by lia. zstep. zstep. zstep. rewrite ?Z.ltb_irrefl. if_false.
  zstep. zstep. if_false. zstep. zstep. zstep.
  release_frame FR1 ST (usp + -192). release_frame FR0 ST (usp + -176).
  try replace (8 + A8) with (A8 + 8) in * by lia.
  replace (usp + -176) with (usp - 176) in * by lia. replace (usp + -160) with (usp - 160) in * by lia. replace (usp + -112) with (usp - 112) in * by lia.
  replace (usp + -96) with (usp - 96) in * by lia. replace (usp + -88) with (usp - 88) in * by lia. replace (usp + -80) with (usp - 80) in * by lia.
  apply evt_done. eexists _, _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [exact CH|]. split; [exact FR|]. split; [exact F1|]. split; [exact F1b| exact F0].
Qed.

Lemma pb_walk3 : forall (usp lo A8 : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j2 : list byte) F fc (m : mem),
  stk bsegs m lo (usp - 176) -> lo <= usp - 208 -> 0x100000000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 < A8 -> A8 + 8 < usp - 208 -> A8 mod 16 = 0 ->
  usp / 8 + 2147451000 <= lo ->
  client_consts m -> pb_statsh m -> pb_stksh usp m ->
  rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  rw_cells bsegs m (usp - 176) [C8 s8; C8 s7] ->
  rw_cells bsegs m (usp - 160) [C8 s6; C8 s5; C8 (wz SHB); C8 (wz 2148333569); C8 (wz IMP_AVP_ARR_A); C8 (wz IMP_VEC_OBJ_A)] ->
  rw_cells bsegs m (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf148)] ->
  rw_cells bsegs m (usp - 96) [CB 8 j2; C8 (wz A8); C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8)); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR (wz 0xbf8d8) (wz (usp - 112)) gp tp t0 t1 t2 (wz (IMP_VEC_OBJ_A + 8)) (wz IMP_VEC_OBJ_A) (wz A8) (wz (A8 + 8)) (wz (A8 + 8)) (wz (A8 + 8)) (wz 1) (wz 0) (wz 0) a7
                   (wz IMP_AVP_ARR_A) (wz 2148333569) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_annot) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 176, usp); (IMP_VEC_OBJ_A, IMP_VEC_OBJ_A + 24)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp - 112)
      /\ rw_cells bsegs m' IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))]
      /\ rw_cells bsegs m' (usp - 96) [CB 8 j2; C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells bsegs m' (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf148)])
    (MS (mkR (wz 0xbf5bc) (wz (usp - 176)) gp tp t0 t1 t2 (wz (usp - 88)) (wz IMP_VEC_OBJ_A) (wz A8) a1 a2 a3 a4 a5 a6 a7
             (wz (IMP_VEC_OBJ_A + 8)) (wz (usp - 80)) (wz A8) (wz SHB) (wz 2148333569) (wz (usp / 8 + 2147450870)) (wz 2148333568) s9 s10 s11 t3 t4 t5 t6) F (wz 0xbf5bc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH U16 A80 A8H A16 USH (CC1 & CC2 & _ & _) (SA8 & SA9 & SAA & SDC) (SK1 & SK2 & SK3 & SK4 & SK5) VEC F2 F1 F1b F0 MI.
  unfold IMP_VEC_OBJ_A, IMP_AVP_ARR_A, e_annot, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl [(usp - 176, usp); (7061504, 7061504 + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 176)) = usp - 176) by (apply unsigned_lit; lia).
  assert (AL7 : Z.land A8 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
  replace (usp - 176) with (usp + -176) in * by lia. replace (usp - 160) with (usp + -160) in * by lia. replace (usp - 112) with (usp + -112) in * by lia.
  replace (usp - 96) with (usp + -96) in * by lia. replace (usp - 88) with (usp + -88) in * by lia. replace (usp - 80) with (usp + -80) in * by lia.
  zstep. zstep. if_false. zstep. zstep. zstep. if_false. zstep. zstep. if_false.
  zstep. ls. zstep. zstep. zstep. ls. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-72) ) / 8 + 2147450880) with ( usp / 8 + 2147450871 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. ls. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-64) ) / 8 + 2147450880) with ( usp / 8 + 2147450872 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. try rewrite shr3_div. ls. zstep.
  try replace (( usp + (-88) ) / 8 + 2147450880) with ( usp / 8 + 2147450869 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. try replace ( A8 + 8 - A8 ) with 8 by lia. zstep. ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. ls. ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K]. zstep. zstep. zstep. zstep. unz. if_false.
  change (Z.lxor 1 0 ) with 1 . zstep. zstep. zstep. zstep. unz. if_false.
  zstep. zstep. zstep. zstep. zstep. if_false. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K]. zstep.
  zstep. ls. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K]. zstep. zstep. zstep. zstep. unz. if_false.
  change (Z.lxor 1 0 ) with 1 . zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K]. zstep. zstep. zstep.
  release_frame F2 ST (usp + -160). release_frame F1 ST (usp + -112).
  try replace (8 + A8) with (A8 + 8) in * by lia.
  replace (usp + -176) with (usp - 176) in * by lia. replace (usp + -112) with (usp - 112) in * by lia. replace (usp + -96) with (usp - 96) in * by lia.
  apply evt_done. eexists _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [exact VEC|]. split; [exact F0| exact F1b].
Qed.

Lemma pb_walk4 : forall (usp lo A8 : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j2 : list byte) F fc (m : mem),
  stk bsegs m lo (usp - 112) -> lo <= usp - 208 -> 0x100000000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 < A8 -> A8 + 8 < usp - 208 -> A8 mod 16 = 0 ->
  usp / 8 + 2147451000 <= lo ->
  client_consts m -> pb_statsh m -> pb_stksh usp m ->
  rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))] ->
  rw_cells bsegs m (usp - 96) [CB 8 j2; C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf148)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz (A8 + 8)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 112, usp); (IMP_VEC_OBJ_A + 8, IMP_VEC_OBJ_A + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))])
    (MS (mkR (wz 0xbf8d8) (wz (usp - 112)) gp tp t0 t1 t2 (wz (IMP_VEC_OBJ_A + 8)) (wz IMP_VEC_OBJ_A) a0 a1 (wz (A8 + 8)) a3 a4 a5 a6 a7
             (wz IMP_AVP_ARR_A) (wz 2148333569) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0xbf8d8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH U16 A80 A8H A16 USH (CC1 & CC2 & _ & _) (SA8 & SA9 & SAA & SDC) (SK1 & SK2 & SK3 & SK4 & SK5) VEC F0 F1 MI.
  unfold IMP_VEC_OBJ_A, IMP_AVP_ARR_A, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *. change (7061504 + 8) with 7061512 in *.
  pose proof (munch_refl [(usp - 112, usp); (7061512, 7061504 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 112)) = usp - 112) by (apply unsigned_lit; lia).
  assert (AL7 : Z.land A8 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
  replace (usp - 112) with (usp + -112) in * by lia. replace (usp - 96) with (usp + -96) in * by lia.
  zstep. zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. zstep. zstep. ls. zstep. zstep. zstep. zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-80) ) / 8 + 2147450880) with ( usp / 8 + 2147450870 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. try rewrite shr3_div. zstep.
  try replace (( usp + (-72) ) / 8 + 2147450880) with ( usp / 8 + 2147450871 ) by (Z.div_mod_to_equations; lia). zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. try rewrite shr3_div. zstep. if_true.
  zstep. try rewrite shr3_div. zstep. try replace (( usp + (-88) ) / 8 + 2147450880) with ( usp / 8 + 2147450869 ) by (Z.div_mod_to_equations; lia).
  zstep. zstep. if_false. zstep. zstep. if_true. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame F1 ST (usp + -96). release_frame F0 ST usp.
  replace (usp + -112) with (usp - 112) in * by lia.
  apply evt_done. eexists _, _, _, _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact VEC].
Qed.

Section PB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.

Hypothesis AF_IXIT : forall Σ m, ART RT Σ m -> ixit_rt (rt_sp0 RT Σ) m.

Hypothesis AF_LVM : forall Σ m p k, ART RT Σ m -> In (p, k) (rt_live RT Σ) ->
  (0 <= p /\ p + k <= 0x7fff8000) \/ (0x10007fff7fff < p /\ p + k <= 0x800000000000).
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma pb_statsh_art : forall Σ m, ART RT Σ m -> pb_statsh m.
Proof using AF.
  intros Σ m HA.
  pose proof (shz_static RT AF Σ m IMP_VEC_OBJ_A 24 HA eq_refl ltac:(unfold IMP_VEC_OBJ_A; lia) eq_refl
                ltac:(intros i Hi; unfold IMP_VEC_OBJ_A; split; [apply client_static_intro; lia| lia])) as S1.
  pose proof (shz_static RT AF Σ m IMP_AVP_ARR_A 8 HA eq_refl ltac:(unfold IMP_AVP_ARR_A; lia) eq_refl
                ltac:(intros i Hi; unfold IMP_AVP_ARR_A; split; [apply client_static_intro; lia| lia])) as S2.
  unfold pb_statsh, IMP_VEC_OBJ_A, IMP_AVP_ARR_A in *.
  change 2148333568 with (shad 7061504). change 2148333569 with (shad 7061512). change 2148333570 with (shad 7061520). change 2148333620 with (shad 7061920).
  refine (conj _ (conj _ (conj _ _))); (apply shz_ro1; [| reflexivity| lia]); first [exact S2 | eapply shz_sub; [exact S1| lia| lia]].
Qed.

Lemma pb_stksh_art : forall Σ m usp, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN + 104 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 -> pb_stksh usp m.
Proof using AF.
  intros Σ m usp HA LO HI U16.
  pose proof (shz_stack RT AF Σ m (usp - 88) 40 HA ltac:(lia) ltac:(lia) ltac:(ul)) as S. unfold pb_stksh.
  pose proof (af_sp0_range RT AF Σ m HA) as R.
  replace (usp / 8 + 2147450869) with (shad (usp - 88)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  replace (usp / 8 + 2147450870) with (shad (usp - 80)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  replace (usp / 8 + 2147450871) with (shad (usp - 72)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  replace (usp / 8 + 2147450872) with (shad (usp - 64)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  replace (usp / 8 + 2147450873) with (shad (usp - 56)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  refine (conj _ (conj _ (conj _ (conj _ _)))); (apply shz_ro1; [eapply shz_sub; [exact S| lia| lia]| Z.div_mod_to_equations; lia| ul]).
Qed.

Lemma ixit_annot_cells : forall sp0 m, ixit_rt sp0 m ->
  rw_cells bsegs m g_GOT_flags [C8 (Z_to_bv 64 0x187178)] /\ ro_cells bsegs m g_flags_dco [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m g_GOT_verbosity [C8 (Z_to_bv 64 g_verbosity)] /\ rw_cells bsegs m g_verbosity [C4 (Z_to_bv 64 0)].
Proof.
  intros sp0 m H. unfold ixit_rt in H.
  destruct H as (_ & _ & _ & GF & _ & _ & _ & _ & _ & _ & _ & FD & GV & VV & _). exact (conj GF (conj FD (conj GV VV))).
Qed.

Section WithPM.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma pushbackA : forall Σ (K : config -> Prop) (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo usp ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 176 + RT_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  tp = wz TPV_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost 8 <= rt_credit RT Σ ->
  rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)] ->
  (forall (Σ' : rts RT) (A8 : Z) (a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) F' (m' : mem),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo usp ->
     rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) usp IMP_VEC_OBJ_A 24 m m' ->
     rt_live RT Σ' = (A8, 8) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - mcost 8 -> 0 < A8 -> A8 mod 16 = 0 ->
     rw_cells bsegs m' IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))] -> rw_cells bsegs m' A8 [C8 (wz SJ_SINGLETON)] ->
     aevt Σ' K (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 (wz (A8 + 8)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz IMP_VEC_OBJ_A) (wz IMP_AVP_ARR_A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xbf038 m).
Proof using AF RC AF_IXIT AF_LVM FDO MST.
  intros until m. intros ART0 MI0 ST0 LOW LOSP SPA U16 ETP LV CR VEC0 ARR0 HK. unfold RT_STACK in LOSP. subst tp.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (GLO : 0x100000000 <= lo) by ul. assert (SPH : usp < 2^63) by ul.
  assert (USH : usp / 8 + 2147451000 <= lo) by (clear - LOW LOSP SPA SP0W; unfold USTACK_TOP, STACK_WIN, RT_STACK in *; Z.div_mod_to_equations; lia).
  assert (SPLIT : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m usp a ART0 Ha); [left; lia| right; lia]. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pb_walk1 usp lo ra gp _ t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) GLO SPH U16
                             (af_client_consts RT AF Σ m ART0) (pb_statsh_art Σ m ART0) (pb_stksh_art Σ m usp ART0 ltac:(ul) SPA U16) VEC0 MI0)|].
  cbv beta. intros ms1 (m1 & j0 & j1 & -> & MU1 & WM1 & MI1 & ST1 & F48a & F16a & F96a). apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 176) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (AG1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (IMP_VEC_OBJ_A <= bv_unsigned a < IMP_VEC_OBJ_A + 24) -> m1 a = m a).
  { intros a Ha Hn. apply MU1. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| exact I]. }
  assert (VEC1 : rw_cells bsegs m1 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact VEC0|]. intros a Ha. apply MU1. cbn [outside cells_size csize Nat.add] in *. unfold IMP_VEC_OBJ_A in *. split; [ul| exact I]. }
  assert (ARR1 : rw_cells bsegs m1 IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)]).
  { eapply rw_cells_agree_nw; [exact ARR0|]. intros a Ha. apply MU1. cbn [outside cells_size csize Nat.add] in *. unfold IMP_AVP_ARR_A in *. split; [ul| exact I]. }
  clear MU1 VEC0 ARR0.

  eapply (aevt_opnew RT AF RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (usp - 160) 8 lo ltac:(lia) eq_refl LV CR ART1 MI1 ST1 LOW
            ltac:(ul) ltac:(ul) ltac:(clear - U16; Z.div_mod_to_equations; lia)).
  intros Σ1 p u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 m2 ART2 MI2 WM2 ST2 PRES2 WR2 ACC2 LV1 FRS1 SP1 CR1 P0 P16 PTOP.
  rewrite (ret_pc_even 0xbf3e0) by lia.
  pose proof (af_live_range RT AF Σ1 m2 p 8 ART2 ltac:(rewrite LV1; left; reflexivity)) as (_ & PZ & PSG). rewrite SP1 in PZ.
  pose proof (AF_LVM Σ1 m2 p 8 ART2 ltac:(rewrite LV1; left; reflexivity)) as LVM.
  assert (FRESH : forall sp a, lo <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> ~ (p <= a < p + 8)).
  { intros sp a Hsp Ha. apply (fresh_apart_l RT AF Σ1 m2 [(p, 8)] (rt_live RT Σ) p 8 sp a ART2 LV1 ltac:(left; reflexivity) ltac:(rewrite SP1; lia)).
    rewrite FRS1. exact Ha. }
  assert (LIVE_SUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; right; exact He).
  assert (FRM_SUB : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ1)) by (intros e He; rewrite FRS1; exact He).
  assert (AG2 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (IMP_VEC_OBJ_A <= bv_unsigned a < IMP_VEC_OBJ_A + 24) -> m2 a = m a).
  { intros a Ha Hn. rewrite <- (AG1 a Ha Hn). apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]. }
  assert (T2 : forall P : Z -> Prop, (forall x, P x -> (usp - 160 <= x < usp) \/ (IMP_VEC_OBJ_A <= x < IMP_VEC_OBJ_A + 24) \/ (IMP_AVP_ARR_A <= x < IMP_AVP_ARR_A + 8)) -> agree_on P m1 m2).
  { intros P HP. apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. destruct (HP _ Hx) as [H|[H|H]]; [left; ul| right; left| right; left];
      apply client_static_intro; unfold IMP_VEC_OBJ_A, IMP_AVP_ARR_A in H; lia. }
  assert (F48b : rw_cells bsegs m2 (usp - 160) [CB 8 j1; C8 s5; C8 (wz SHB); C8 (wz 2148333569); C8 (wz IMP_AVP_ARR_A); C8 (wz IMP_VEC_OBJ_A)]).
  { eapply rw_cells_agree_nw; [exact F48a|]. apply T2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (F16b : rw_cells bsegs m2 (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf0f0)]).
  { eapply rw_cells_agree_nw; [exact F16a|]. apply T2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (F96b : rw_cells bsegs m2 (usp - 96) [CB 32 j0; C8 (wz 0); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact F96a|]. apply T2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (VEC2 : rw_cells bsegs m2 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact VEC1|]. apply T2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia. }
  assert (ARR2 : rw_cells bsegs m2 IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)]).
  { eapply rw_cells_agree_nw; [exact ARR1|]. apply T2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right. lia. }
  destruct (wr_at_rw_CB m2 p 8 WR2 ltac:(lia)) as (jc & CH2). change (Z.to_nat 8) with 8%nat in CH2.
  assert (CS2 : ro_cells bsegs m2 (p / 8 + 2147450880) [C1 z8]).
  { change (p / 8 + 2147450880) with (shad p). apply shz_ro1; [| lia| ul].
    exact (shz_live RT AF Σ1 m2 p 8 ART2 ltac:(rewrite LV1; left; reflexivity) ltac:(clear - P16; Z.div_mod_to_equations; lia)). }
  assert (ASK : p + 8 <= usp / 8 + 2147450860 \/ usp / 8 + 2147450880 <= p).
  { clear - LVM LOW LOSP SPA SP0W. unfold USTACK_TOP, STACK_WIN, RT_STACK in *. Z.div_mod_to_equations. lia. }
  clear T2 F48a F16a F96a VEC1 ARR1 AG1 PRES2 WM1 MI1 ST1 ART1.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pb_walk2 usp lo p ra gp _ u0 u1 u2 s0 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 j0 j1 jc F1 fc m2
                             ST2 ltac:(ul) GLO SPH U16 P0 ltac:(ul) P16 ltac:(ul) ltac:(lia) USH ltac:(ul) ASK
                             (af_client_consts RT AF Σ1 m2 ART2) (pb_statsh_art Σ1 m2 ART2) (pb_stksh_art Σ1 m2 usp ART2 ltac:(ul) SPA U16)
                             VEC2 (proj1 ARR2) CH2 CS2 F48b F16b F96b MI2)|].
  cbv beta. intros ms3 (m3 & a3' & a4' & a5' & a6' & j2 & -> & MU3 & WM3 & MI3 & ST3 & CH3 & F16c & F48c & F16bc & F96c). apply evt_done.
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 (usp - 208) ART2 ltac:(rewrite SP1; ul)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - left. ul.
    - right; right; left. exists p, 8. split; [rewrite LV1; left; reflexivity| lia]. }
  assert (AG3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (IMP_VEC_OBJ_A <= bv_unsigned a < IMP_VEC_OBJ_A + 24) -> m3 a = m a).
  { intros a Ha Hn. rewrite <- (AG2 a Ha Hn). apply MU3. cbn [outside]. pose proof (SPLIT _ Ha). pose proof (FRESH usp _ ltac:(lia) Ha). split; [lia| split; [lia| exact I]]. }
  assert (VEC3 : rw_cells bsegs m3 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact VEC2|]. intros a Ha. apply MU3. cbn [outside cells_size csize Nat.add] in *. unfold IMP_VEC_OBJ_A, SEGTOP_A in *. lia. }
  clear MU3 VEC2 ARR2 CH2 CS2 F48b F16b F96b AG2 WM2 MI2 ST2 WM3.

  assert (EU176 : bv_unsigned (Z_to_bv 64 (usp - 176)) = usp - 176) by (apply unsigned_lit; lia).
  assert (BY0 : bytes_at bsegs m3 0 (@nil byte)) by (split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn [length] in Hi; lia).
  assert (CSRC : checked_src RT Σ1 m3 (wz (usp - 176)) lo 0 (Z.of_nat (@length byte nil))).
  { unfold checked_src. cbn [length Z.of_nat]. split; [intros H; lia| left; lia]. }
  assert (CDST : checked_dst RT Σ1 m3 (wz (usp - 176)) p (Z.of_nat (@length byte nil))).
  { unfold checked_dst. cbn [length Z.of_nat]. split; [intros H; lia|]. split; [intros i Hi; lia|]. split; [lia|]. split; [ul|]. intros i Hi. lia. }
  assert (COK : call_ok RT Σ1 m3 (wz (usp - 176)) lo).
  { unfold call_ok. rewrite EU176, SP1. split; [exact ST3|]. split; [lia|]. split; [ul|]. split; [ul| clear - U16; Z.div_mod_to_equations; lia]. }
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m3 p 0 (@nil byte) lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) ltac:(cbn; lia) BY0 CSRC CDST ltac:(right; cbn; lia) ART3 MI3 COK).
  intros v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 m4 (ART4 & MI4 & WM4 & ST4) PR4 _. rewrite EU176 in ST4, PR4. cbn [length Z.of_nat] in PR4.
  rewrite (ret_pc_even 0xbf5bc) by lia.
  assert (T4 : forall P : Z -> Prop, (forall x, P x -> (usp - 176 <= x < usp) \/ (IMP_VEC_OBJ_A <= x < IMP_VEC_OBJ_A + 24) \/ (p <= x < p + 8)) -> agree_on P m3 m4).
  { intros P HP. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR4). intros x Hx. split; [| lia]. destruct (HP _ Hx) as [H|[H|H]].
    - left. ul. - right; left. apply client_static_intro. unfold IMP_VEC_OBJ_A in H. lia. - right; right; left. exists p, 8. split; [rewrite LV1; left; reflexivity| lia]. }
  assert (AG4 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (IMP_VEC_OBJ_A <= bv_unsigned a < IMP_VEC_OBJ_A + 24) -> m4 a = m a).
  { intros a Ha Hn. rewrite <- (AG3 a Ha Hn). apply PR4; [| lia]. apply (aclient_mono _ _ _ _ _ _ _ Ha LIVE_SUB FRM_SUB). lia. }
  assert (VEC4 : rw_cells bsegs m4 IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
  { eapply rw_cells_agree_nw; [exact VEC3|]. apply T4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; left. lia. }
  assert (F16d : rw_cells bsegs m4 (usp - 176) [C8 s8; C8 s7]).
  { eapply rw_cells_agree_nw; [exact F16c|]. apply T4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (F48d : rw_cells bsegs m4 (usp - 160) [C8 s6; C8 s5; C8 (wz SHB); C8 (wz 2148333569); C8 (wz IMP_AVP_ARR_A); C8 (wz IMP_VEC_OBJ_A)]).
  { eapply rw_cells_agree_nw; [exact F48c|]. apply T4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (F16bd : rw_cells bsegs m4 (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf148)]).
  { eapply rw_cells_agree_nw; [exact F16bc|]. apply T4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (F96d : rw_cells bsegs m4 (usp - 96) [CB 8 j2; C8 (wz p); C8 (wz p); C8 (wz (p + 8)); C8 (wz (p + 8)); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact F96c|]. apply T4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (CH4 : rw_cells bsegs m4 p [C8 (wz SJ_SINGLETON)]).
  { eapply rw_cells_agree_nw; [exact CH3|]. apply T4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right. lia. }
  clear T4 PR4 VEC3 F16c F48c F16bc F96c CH3 AG3 WM4 MI3 ST3 ART3.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pb_walk3 usp lo p ra gp _ v0 v1 v2 s0 s1 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 j2 F2 fc m4
                             ST4 ltac:(ul) GLO SPH U16 P0 ltac:(ul) P16 USH
                             (af_client_consts RT AF Σ1 m4 ART4) (pb_statsh_art Σ1 m4 ART4) (pb_stksh_art Σ1 m4 usp ART4 ltac:(ul) SPA U16) VEC4 F16d F48d F16bd F96d MI4)|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & ST5 & VEC5 & F96e & F16e).
  assert (ART5 : ART RT Σ1 m5).
  { apply (art_client_write RT AF Σ1 m4 m5 (usp - 176) ART4 ltac:(rewrite SP1; ul)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - left. ul.
    - right; left. apply client_static_intro. unfold IMP_VEC_OBJ_A in Hin. lia. }
  assert (AG5 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (IMP_VEC_OBJ_A <= bv_unsigned a < IMP_VEC_OBJ_A + 24) -> m5 a = m a).
  { intros a Ha Hn. rewrite <- (AG4 a Ha Hn). apply MU5. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| split; [lia| exact I]]. }
  assert (CH5 : rw_cells bsegs m5 p [C8 (wz SJ_SINGLETON)]).
  { eapply rw_cells_agree_nw; [exact CH4|]. intros a Ha. apply MU5. cbn [outside cells_size csize Nat.add] in *. unfold IMP_VEC_OBJ_A, SEGTOP_A in *. lia. }
  clear MU5 WM5 VEC4 F16d F48d F16bd F96d CH4 AG4 MI4 ST4 ART4.

  destruct (ixit_annot_cells _ _ (AF_IXIT Σ1 m5 ART5)) as (GF & FD & GV & VV).
  eapply evt_cut; [eapply (annot_nopA (usp - 112) lo p (p + 8) (p + 8) (wz 0xbf8d8) gp _ v0 v1 v2 (wz (IMP_VEC_OBJ_A + 8)) (wz IMP_VEC_OBJ_A) (wz 1) (wz 0) (wz 0) c7
                             (wz IMP_AVP_ARR_A) (wz 0x800cf801) (wz SHB) s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F2 fc m5
                             ST5 ltac:(unfold ANNOT_FRAME; ul) GLO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ul) ltac:(lia) GF FD GV VV MI5)|].
  cbv beta. intros ms6 (e0 & e1 & e3 & m6 & -> & MU6 & WM6 & MI6 & ST6). apply evt_done.
  unfold ANNOT_FRAME in MU6. rewrite (ret_pc_even 0xbf8d8) by lia.
  assert (ART6 : ART RT Σ1 m6).
  { apply (art_client_write RT AF Σ1 m5 m6 (usp - 112 - 2128) ART5 ltac:(rewrite SP1; ul)); [| exact WM6].
    intros a Ha. apply MU6. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (AG6 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (IMP_VEC_OBJ_A <= bv_unsigned a < IMP_VEC_OBJ_A + 24) -> m6 a = m a).
  { intros a Ha Hn. rewrite <- (AG5 a Ha Hn). apply MU6. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| exact I]. }
  assert (T6 : forall P : Z -> Prop, (forall x, P x -> (usp - 112 <= x < usp) \/ (x < lo)) -> agree_on P m5 m6).
  { intros P HP a Ha. apply MU6. cbn [outside]. pose proof (HP _ Ha). split; [lia| exact I]. }
  assert (VEC6 : rw_cells bsegs m6 IMP_VEC_OBJ_A [C8 (wz p); C8 (wz (p + 8)); C8 (wz (p + 8))]).
  { eapply rw_cells_agree_nw; [exact VEC5|]. apply T6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold IMP_VEC_OBJ_A in Hx. right. ul. }
  assert (F96f : rw_cells bsegs m6 (usp - 96) [CB 8 j2; C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz IMP_VEC_OBJ_A); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree_nw; [exact F96e|]. apply T6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (F16f : rw_cells bsegs m6 (usp - 112) [C8 (wz (IMP_VEC_OBJ_A + 8)); C8 (wz 0xbf148)]).
  { eapply rw_cells_agree_nw; [exact F16e|]. apply T6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (CH6 : rw_cells bsegs m6 p [C8 (wz SJ_SINGLETON)]).
  { eapply rw_cells_agree_nw; [exact CH5|]. apply T6. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right. lia. }
  clear T6 MU6 WM6 VEC5 F96e F16e CH5 AG5 MI5 ST5 ART5 GF FD GV VV.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pb_walk4 usp lo p ra gp _ v0 v1 v2 s0 s1 e0 e1 e3 _ (wz 0) (wz 0) c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 j2 F2 fc m6
                             ST6 ltac:(ul) GLO SPH U16 P0 ltac:(ul) P16 USH
                             (af_client_consts RT AF Σ1 m6 ART6) (pb_statsh_art Σ1 m6 ART6) (pb_stksh_art Σ1 m6 usp ART6 ltac:(ul) SPA U16) VEC6 F96f F16f MI6)|].
  cbv beta. intros ms7 (d1 & d2 & d3 & d4 & d5 & d6 & d7 & m7 & -> & MU7 & WM7 & MI7 & ST7 & VEC7). apply evt_done.
  assert (ART7 : ART RT Σ1 m7).
  { apply (art_client_write RT AF Σ1 m6 m7 (usp - 112) ART6 ltac:(rewrite SP1; ul)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - left. ul.
    - right; left. apply client_static_intro. unfold IMP_VEC_OBJ_A in Hin. lia. }
  assert (AG7 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> ~ (IMP_VEC_OBJ_A <= bv_unsigned a < IMP_VEC_OBJ_A + 24) -> m7 a = m a).
  { intros a Ha Hn. rewrite <- (AG6 a Ha Hn). apply MU7. cbn [outside]. pose proof (SPLIT _ Ha). split; [lia| split; [lia| exact I]]. }
  assert (CH7 : rw_cells bsegs m7 p [C8 (wz SJ_SINGLETON)]).
  { eapply rw_cells_agree_nw; [exact CH6|]. intros a Ha. apply MU7. cbn [outside cells_size csize Nat.add] in *. unfold IMP_VEC_OBJ_A, SEGTOP_A in *. lia. }
  exact (HK Σ1 p d1 d2 d3 d4 d5 d6 d7 v0 v1 v2 v3 v4 v5 v6 F2 m7 ART7 MI7 ST7 AG7 LV1 FRS1 SP1 CR1 P0 P16 VEC7 CH7).
Qed.
End WithPM.
End PB.
