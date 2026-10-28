(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes Mem ImageA RzCPS SysStep StoreFast FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit X_aexdefs X_ixdefs X_vecxdefs Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit4A Atp_hkit5A Atp_fzwA Pj_defsA Pj_rtkA R_cache_defs R_prim_defs R_m2s R_setshadow R_poison Imp_annotA Imp_annot2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition vx_statsh (m : mem) : Prop :=
  ro_cells bsegs m 0x800cf800 [C1 z8] /\ ro_cells bsegs m 0x800cf801 [C1 z8] /\ ro_cells bsegs m 0x800cf802 [C1 z8].

Lemma b2z_pos : forall x, 0 < x -> Z.b2z (0 <? x) = 1.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, 0 < x -> Z.b2z (x <? 1) = 0.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Local Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Lemma vx_walk1 : forall (usp lo p : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 80 -> 0x100000000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 < p -> p + 16 < 2^63 ->
  client_consts m -> vx_statsh m -> ro_cells bsegs m (usp / 8 + 2147450878) [C1 z8] ->
  rw_cells bsegs m AEX_VEC_OBJ [C8 (wz p); C8 (wz (p + 8)); C8 (wz (p + 8))] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR (wz 0xbeea8) (wz (usp - 64)) gp tp t0 t1 t2 (wz (usp - 16)) (wz SHB) (wz p) (wz (p + 8)) (wz (p + 8)) (wz p) (wz 1) (wz 0) (wz 882689) a7
                   (wz (usp / 8 + 2147450878)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_annot) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 80, usp); (AEX_VEC_OBJ + 8, AEX_VEC_OBJ + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp - 64)
      /\ rw_cells bsegs m' (usp - 16) [C8 (wz AEX_VEC_OBJ); C8 ra]
      /\ rw_cells bsegs m' (usp - 48) [C8 s2; C8 s1; C8 s0; C8 (wz 0xb4c64)]
      /\ rw_cells bsegs m' (usp - 64) [C8 (wz (usp - 16)); C8 (wz 0xbec14)]
      /\ rw_cells bsegs m' AEX_VEC_OBJ [C8 (wz p); C8 (wz p); C8 (wz (p + 8))])
    (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz AEX_VEC_OBJ) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz X_VECDTOR) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH U16 P0 PH (CC1 & CC2 & _ & _) (SA8 & SA9 & SAA) SKE VEC MI.
  unfold AEX_VEC_OBJ, X_VECDTOR, e_annot, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl [(usp - 80, usp); (7061504 + 8, 7061504 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
  ls. ls. zstep. zstep.

  zstep. carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  repeat match type of FR0 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR0; clearbody j end.
  ls. ls. ls. ls. zstep. zstep. zstep. zstep. zstep. try rewrite shr3_div. zstep.
  try replace ((usp + -16) / 8 + 2147450880) with (usp / 8 + 2147450878) by (Z.div_mod_to_equations; lia).
  try replace (2147450880 + (usp + -16) / 8) with (usp / 8 + 2147450878) by (Z.div_mod_to_equations; lia).
  zstep. shz_norm. zstep. if_false.

  zstep. zstep. if_false. zstep. zstep. if_false.
  zstep. try rewrite shr3_div. zstep. try change (7061504 / 8 + 2147450880) with 2148333568. try change (2147450880 + 7061504 / 8) with 2148333568.
  zstep. shz_norm. zstep. if_false.
  zstep. step. if_cases K; zify_cond K; [exfalso; lia|].
  zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app] in FR1.
  repeat match type of FR1 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR1; clearbody j end.
  ls. zstep. zstep. zstep. zstep.
  zstep. try rewrite shr3_div. zstep. try change (7061512 / 8 + 2147450880) with 2148333569. try change (2147450880 + 7061512 / 8) with 2148333569.
  zstep. shz_norm. zstep. if_false.
  zstep. try rewrite shr3_div. zstep. try change (7061504 / 8 + 2147450880) with 2148333568. try change (2147450880 + 7061504 / 8) with 2148333568.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. step. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep. zstep. step. if_cases K3; zify_cond K3; [exfalso; lia|].
  zstep. step. if_cases K4; zify_cond K4; [exfalso; lia|].
  zstep. shz_norm. zstep. if_false.
  zstep. try replace (p + 8 - p) with 8 by lia. zstep. try change (Z.shiftr 8 3) with 1. ls.
  zstep. zstep. release_frame FR1 ST (usp + -48). zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app] in FR1.
  repeat match type of FR1 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR1; clearbody j end.
  ls. ls. zstep. zstep. zstep.
  zstep. try rewrite shr3_div. zstep. try change (7061504 / 8 + 2147450880) with 2148333568. try change (2147450880 + 7061504 / 8) with 2148333568.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. try change (Z.shiftl 1 3) with 8. zstep.
  zstep. zstep. unz. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. if_false.
  step. if_cases K5; zify_cond K5; [exfalso; lia|].
  zstep. zstep. try rewrite shr3_div. try change (7061512 / 8) with 882689. zstep. try change (882689 + 2147450880) with 2148333569. try change (2147450880 + 882689) with 2148333569.
  zstep. shz_norm. zstep. if_false.
  zstep. step. if_cases K6; zify_cond K6; [exfalso; lia|].
  zstep. unz. zstep. try change (Z.lxor 1 0) with 1. zstep. if_false.
  zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR2; [| reflexivity]. cbn [mk_CB_cells app] in FR2.
  repeat match type of FR2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR2; clearbody j end.
  ls. zstep. zstep. zstep. zstep.
  zstep. try rewrite shr3_div. zstep. try change (7061504 / 8 + 2147450880) with 2148333568. try change (2147450880 + 7061504 / 8) with 2148333568.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. try rewrite shr3_div. try change (7061520 / 8) with 882690. zstep. try change (882690 + 2147450880) with 2148333570. try change (2147450880 + 882690) with 2148333570.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. step. if_cases K7; zify_cond K7; [exfalso; lia|].
  zstep. zstep. unz. zstep. try change (Z.lxor 1 0) with 1. zstep. if_false.
  step. if_cases K8; zify_cond K8; [exfalso; lia|].
  zstep. zstep. release_frame FR2 ST (usp + -64). zstep.
  try replace (usp + -64) with (usp - 64) in * by lia. try replace (usp + -48) with (usp - 48) in * by lia. try replace (usp + -16) with (usp - 16) in * by lia.
  apply evt_done. eexists _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [exact FR|]. split; [exact FR0|]. split; [exact FR1| eassumption].
Qed.

Lemma vx_walk2 : forall (usp lo p : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo (usp - 64) -> lo <= usp - 80 -> 0x100000000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 < p -> p + 16 < 2^63 ->
  client_consts m -> vx_statsh m -> ro_cells bsegs m (usp / 8 + 2147450878) [C1 z8] ->
  rw_cells bsegs m AEX_VEC_OBJ [C8 (wz p); C8 (wz p); C8 (wz (p + 8))] ->
  rw_cells bsegs m (usp - 16) [C8 (wz AEX_VEC_OBJ); C8 ra] ->
  rw_cells bsegs m (usp - 64) [C8 (wz (usp - 16)); C8 (wz 0xbec14)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR (wz 0xbede8) (wz (usp - 64)) gp tp t0 t1 t2 (wz (usp - 16)) (wz SHB) (wz p) (wz (p + 8)) (wz p) (wz (p + 8)) (wz 1) (wz 0) (wz 882690) a7
                   (wz (usp / 8 + 2147450878)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_annot) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 80, usp - 48)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp - 64)
      /\ rw_cells bsegs m' (usp - 64) [C8 (wz (usp - 16)); C8 (wz 0xbec30)])
    (MS (mkR (wz 0xbeea8) (wz (usp - 64)) gp tp t0 t1 t2 (wz (usp - 16)) (wz SHB) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (usp / 8 + 2147450878)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0xbeea8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH U16 P0 PH (CC1 & CC2 & _ & _) (SA8 & SA9 & SAA) SKE VEC F16 F64 MI.
  unfold AEX_VEC_OBJ, e_annot, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl [(usp - 80, usp - 48)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 64)) = usp - 64) by (apply unsigned_lit; lia).
  replace (usp - 64) with (usp + -64) in * by lia. replace (usp - 48) with (usp + -48) in * by lia. replace (usp - 16) with (usp + -16) in * by lia.

  zstep. zstep. zstep. release_frame F64 ST (usp + -48). zstep.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_false. zstep. zstep. if_false. zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
  ls. ls. zstep. zstep. zstep.
  zstep. try rewrite shr3_div. zstep. try change (7061504 / 8 + 2147450880) with 2148333568. try change (2147450880 + 7061504 / 8) with 2148333568.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. try rewrite shr3_div. zstep. try change (7061512 / 8 + 2147450880) with 2148333569. try change (2147450880 + 7061512 / 8) with 2148333569.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. step. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep. zstep. unz. zstep. try change (Z.lxor 1 0) with 1. zstep. if_false.
  zstep. zstep. try rewrite shr3_div. try change (7061520 / 8) with 882690. zstep. try change (882690 + 2147450880) with 2148333570. try change (2147450880 + 882690) with 2148333570.
  zstep. shz_norm. zstep. if_false.
  zstep. step. if_cases K2; zify_cond K2; [exfalso; lia|].
  zstep. unz. zstep. try change (Z.lxor 1 0) with 1. zstep. if_false.
  zstep.

  zstep. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  repeat match type of FR0 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR0; clearbody j end.
  ls. zstep. zstep. zstep. zstep.
  zstep. try rewrite shr3_div. zstep. try change (7061504 / 8 + 2147450880) with 2148333568. try change (2147450880 + 7061504 / 8) with 2148333568.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. try rewrite shr3_div. try change (7061520 / 8) with 882690. zstep. try change (882690 + 2147450880) with 2148333570. try change (2147450880 + 882690) with 2148333570.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. step. if_cases K3; zify_cond K3; [exfalso; lia|].
  zstep. zstep. unz. zstep. try change (Z.lxor 1 0) with 1. zstep. if_false.
  step. if_cases K4; zify_cond K4; [exfalso; lia|].
  zstep. zstep. release_frame FR0 ST (usp + -64). zstep.
  try replace (usp + -64) with (usp - 64) in * by lia. try replace (usp + -48) with (usp - 48) in * by lia. try replace (usp + -16) with (usp - 16) in * by lia.
  apply evt_done. eexists _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma vx_walk3 : forall (usp lo p : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo (usp - 64) -> lo <= usp - 64 -> 0x100000000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 < p -> p + 16 < 2^63 ->
  client_consts m -> vx_statsh m -> ro_cells bsegs m (usp / 8 + 2147450878) [C1 z8] ->
  rw_cells bsegs m AEX_VEC_OBJ [C8 (wz p); C8 (wz p); C8 (wz (p + 8))] ->
  rw_cells bsegs m (usp - 16) [C8 (wz AEX_VEC_OBJ); C8 ra] ->
  rw_cells bsegs m (usp - 48) [C8 s2; C8 s1; C8 s0; C8 (wz 0xb4c64)] ->
  rw_cells bsegs m (usp - 64) [C8 (wz (usp - 16)); C8 (wz 0xbec30)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a2' : word),
      ms = MS (mkR (wz 0xb4c64) (wz (usp - 16)) gp tp t0 t1 t2 s0 s1 (wz p) (wz 8) a2' a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz OPDEL_A) fc None m (seg_rom bsegs)
      /\ stk bsegs m lo (usp - 16))
    (MS (mkR (wz 0xbede8) (wz (usp - 64)) gp tp t0 t1 t2 (wz (usp - 16)) (wz SHB) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (usp / 8 + 2147450878)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0xbede8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH U16 P0 PH (CC1 & CC2 & _ & _) (SA8 & SA9 & SAA) SKE VEC F16 F48 F64 MI.
  unfold AEX_VEC_OBJ, OPDEL_A, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB, z8 in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 64)) = usp - 64) by (apply unsigned_lit; lia).
  replace (usp - 64) with (usp + -64) in * by lia. replace (usp - 48) with (usp + -48) in * by lia. replace (usp - 16) with (usp + -16) in * by lia.

  zstep. zstep. zstep. release_frame F64 ST (usp + -48). zstep.
  zstep. shz_norm. zstep. if_false. zstep.
  zstep. if_false. zstep. zstep. if_false.
  zstep. try rewrite shr3_div. zstep. try change (7061504 / 8 + 2147450880) with 2148333568. try change (2147450880 + 7061504 / 8) with 2148333568.
  zstep. shz_norm. zstep. if_false.

  zstep. zstep. try rewrite shr3_div. zstep. try change (7061520 / 8 + 2147450880) with 2148333570. try change (2147450880 + 7061520 / 8) with 2148333570.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. try replace (p + 8 - p) with 8 by lia.

  zstep. zstep. zstep. zstep. zstep. release_frame F48 ST (usp + -16). zstep.
  apply evt_done. eexists _. split; [cbv delta [mkR]; reflexivity| exact ST].
Qed.

Lemma vx_walk4 : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo (usp - 16) -> lo <= usp - 16 -> 0x100000000 <= lo -> usp < 2^63 ->
  rw_cells bsegs m (usp - 16) [C8 (wz AEX_VEC_OBJ); C8 ra] -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom bsegs)
      /\ stk bsegs m lo usp)
    (MS (mkR (wz 0xb4c64) (wz (usp - 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0xb4c64) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH F16 MI.
  unfold AEX_VEC_OBJ in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 16)) = usp - 16) by (apply unsigned_lit; lia).
  replace (usp - 16) with (usp + -16) in * by lia.
  zstep. zstep. release_frame F16 ST usp. zstep.
  apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
Qed.

Lemma cc_agree : forall (m m' : mem), client_consts m -> agree_on (fun x => x < 0x300000) m m' -> client_consts m'.
Proof.
  intros m m' (C1x & C2x & C3x & C4x) AG. unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  refine (conj _ (conj _ (conj _ _))); (eapply ro_cells_agree; [eassumption|]; eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; lia).
Qed.

Lemma ps_agree : forall (m m' : mem), ps_cells m -> agree_on (fun x => x < 0x300000) m m' -> ps_cells m'.
Proof.
  intros m m' PS AG. destruct PS as (CF & (GOT & SHB0 & HM) & (GRM & RM) & CP & THR).
  unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset in *.
  refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _))));
    (eapply rw_cells_agree_nw; [eassumption|]; eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; lia).
Qed.

Definition ix4 (m : mem) : Prop :=
  rw_cells bsegs m g_GOT_flags [C8 (wz 0x187178)] /\ ro_cells bsegs m g_flags_dco [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m g_GOT_verbosity [C8 (wz g_verbosity)] /\ rw_cells bsegs m g_verbosity [C4 (wz 0)].
Lemma ix4_agree : forall (m m' : mem), ix4 m -> agree_on (fun x => x < 0x300000) m m' -> ix4 m'.
Proof.
  intros m m' (GF & FD & GV & VV) AG. unfold ix4, g_GOT_flags, g_flags_dco, g_GOT_verbosity, g_verbosity in *.
  refine (conj _ (conj _ (conj _ _)));
    first [ eapply rw_cells_agree_nw; [eassumption|] | eapply ro_cells_agree; [eassumption|] ];
    (eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; lia).
Qed.
Lemma ix4_of_ixit : forall sp0 m, ixit_rt sp0 m -> ix4 m /\ ps_cells m.
Proof.
  intros sp0 m H. unfold ixit_rt in H.
  destruct H as (_ & _ & _ & GF & _ & _ & _ & _ & _ & _ & _ & FD & GV & VV & PS). exact (conj (conj GF (conj FD (conj GV VV))) PS).
Qed.

Lemma vx_statsh_agree : forall (m m' : mem), vx_statsh m -> agree_on (fun x => 2148333568 <= x < 2148333571) m m' -> vx_statsh m'.
Proof.
  intros m m' (S1 & S2 & S3) AG. unfold vx_statsh in *.
  refine (conj _ (conj _ _)); (eapply ro_cells_agree; [eassumption|]; eapply agree_sub; [exact AG|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; lia).
Qed.

Lemma raw_byte_of_rw1 : forall (m : mem) a b, img_hull_hi <= a -> a < 2^64 -> rw_cells bsegs m a [CB 1 [b]] -> m (wa a) = Some b.
Proof.
  intros m a b Hlo Hhi [[_ BY] WR].
  cbn [cells_bytes cbytes app] in BY. destruct BY as (_ & _ & BY). specialize (BY 0%nat ltac:(cbn; lia)). cbn [nth_error] in BY. rewrite Z.add_0_r in BY.
  destruct WR as (_ & _ & WR). specialize (WR 0 ltac:(cbn; lia)). rewrite Z.add_0_r in WR.
  unfold mrd in BY. unfold wview in WR. destruct (m (wa a)) as [b'|] eqn:E; [exact BY|].
  exfalso. apply WR. rewrite (find_segment_above bsegs (bv_unsigned (wa a))); [reflexivity| pose proof (bv_unsigned_in_range 64 (wa a)); lia|].
  apply (forallb_mono_top bsegs img_hull_hi); [unfold wa; rewrite unsigned_lit by (unfold img_hull_hi in *; lia); lia| exact asegs_top].
Qed.

Section VX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.

Hypothesis AF_IXIT : forall Σ m, ART RT Σ m -> ixit_rt (rt_sp0 RT Σ) m.

Hypothesis AF_LVM : forall Σ m p k, ART RT Σ m -> In (p, k) (rt_live RT Σ) ->
  (0 <= p /\ p + k <= 0x7fff8000) \/ (0x10007fff7fff < p /\ p + k <= 0x800000000000).

Hypothesis AF_LSW : forall Σ m p k, ART RT Σ m -> In (p, k) (rt_live RT Σ) -> 0 < k -> wr_at bsegs m (shad p) ((k + 7) / 8).
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma vx_statsh_art : forall Σ m, ART RT Σ m -> vx_statsh m.
Proof using AF.
  intros Σ m HA.
  pose proof (shz_static RT AF Σ m AEX_VEC_OBJ 24 HA eq_refl ltac:(unfold AEX_VEC_OBJ; lia) eq_refl
                ltac:(intros i Hi; unfold AEX_VEC_OBJ; split; [apply client_static_intro; lia| lia])) as S1.
  unfold vx_statsh, AEX_VEC_OBJ in *.
  change 2148333568 with (shad 7061504). change 2148333569 with (shad 7061512). change 2148333570 with (shad 7061520).
  refine (conj _ (conj _ _)); (apply shz_ro1; [| reflexivity| lia]); eapply shz_sub; [exact S1| lia| lia| exact S1 |lia|lia| exact S1| lia| lia].
Qed.

Lemma chunk_sh_art : forall Σ m p, ART RT Σ m -> In (p, 8) (rt_live RT Σ) -> p mod 16 = 0 -> rw_cells bsegs m (shad p) [CB 1 [z8]].
Proof using AF AF_LSW.
  intros Σ m p HA HIN P16. pose proof (af_live_range RT AF Σ m p 8 HA HIN) as (P0 & PZ & _). pose proof (af_sp0_range RT AF Σ m HA).
  pose proof (shz_ro1 m p (shz_live RT AF Σ m p 8 HA HIN ltac:(clear - P16; Z.div_mod_to_equations; lia)) ltac:(clear - P16; Z.div_mod_to_equations; lia) ltac:(ul)) as [_ BY].
  cbn [cells_bytes cbytes app] in BY.
  exact (rw_cells_CB_intro m (shad p) [z8] BY (AF_LSW Σ m p 8 HA HIN ltac:(lia))).
Qed.

Theorem vecx_ok : forall PMc, vecx_stmt RT PMc.
Proof using AF RC AF_IXIT AF_LVM AF_LSW.
  intros PMc Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A8 lo
    FDO MST -> ETP HIN A16 VEC0 ART0 MI0 COK LOSP S0LE RAR HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct COK as (ST0 & LOW & LOR & SPA & SP16).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP. rewrite ESP in HK.
  subst tp. unfold kcont in HK. unfold VECX_DEPTH, RT_STACK in LOSP. unfold SEGTOP_A in *.
  assert (GLO : 0x100000000 <= lo) by ul. assert (SPH : usp < 2^63) by ul.
  pose proof (af_live_range RT AF Σ m A8 8 ART0 HIN) as (P0 & PZ & PSG).
  pose proof (AF_LVM Σ m A8 8 ART0 HIN) as LVM.
  assert (D8A : 8 * (A8 / 8) = A8) by (clear - A16; Z.div_mod_to_equations; lia).
  assert (D8U : 8 * (usp / 8) = usp) by (clear - SP16; subst usp; Z.div_mod_to_equations; lia).
  assert (SHP : shad A8 = A8 / 8 + 2147450880) by reflexivity.
  assert (SPLIT : forall Σx mx a, ART RT Σx mx -> rt_sp0 RT Σx = rt_sp0 RT Σ -> aclient (rt_live RT Σx) (rt_frames RT Σx) usp a -> usp <= a \/ a < lo).
  { intros Σx mx a HA HS Ha. destruct (aclient_split_c RT AF Σx mx usp a HA Ha); [left; lia| right; lia]. }
  assert (SKE_OF : forall mx, ART RT Σ mx -> ro_cells bsegs mx (usp / 8 + 2147450878) [C1 z8]).
  { intros mx HA. replace (usp / 8 + 2147450878) with (shad (usp - 16)) by (unfold shad, SHB; clear - D8U; lia).
    apply shz_ro1; [| clear - D8U; Z.div_mod_to_equations; lia| ul]. exact (shz_stack RT AF Σ mx (usp - 16) 8 HA ltac:(ul) ltac:(lia) ltac:(ul)). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (vx_walk1 usp lo A8 ra gp _ t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(lia) GLO SPH SP16 P0 ltac:(ul)
                             (af_client_consts RT AF Σ m ART0) (vx_statsh_art Σ m ART0) (SKE_OF m ART0) VEC0 MI0)|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & F16a & F48a & F64a & VEC1).
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 80) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha; [left; ul| right; left; apply client_static_intro; unfold AEX_VEC_OBJ in Hin; lia]. }
  destruct (ix4_of_ixit _ _ (AF_IXIT Σ m1 ART1)) as ((GF & FD & GV & VV) & PS1).
  pose proof (chunk_sh_art Σ m1 A8 ART1 HIN A16) as SH1.
  pose proof (af_client_consts RT AF Σ m1 ART1) as CC1. pose proof (vx_statsh_art Σ m1 ART1) as SS1. pose proof (SKE_OF m1 ART1) as SK1.

  eapply evt_cut; [eapply (annot_poison8A (usp - 64) lo A8 (wz 0xbeea8) gp _ t0 t1 t2 (wz (usp - 16)) (wz SHB) (wz 1) (wz 0) (wz 882689) a7
                             (wz (usp / 8 + 2147450878)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 [z8] F fc m1
                             ST1 ltac:(unfold ANNOT_FRAME; lia) ltac:(unfold kHighShadowEnd; ul) ltac:(lia) P0 A16 LVM ltac:(ul) GF FD GV VV PS1 SH1 MI1)|].
  cbv beta. intros ms2 (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUP & WMP & MI2 & ST2 & SH2).
  unfold ANNOT_FRAME in MUP. rewrite (ret_pc_even 0xbeea8) by lia.
  assert (T12 : forall P : Z -> Prop, (forall x, P x -> (x + 1 <= usp - 2256 \/ usp - 64 <= x) /\ x <> shad A8) -> agree_on P m1 m2).
  { intros P HP a Ha. apply MUP. cbn [outside]. pose proof (HP _ Ha). split; [lia| split; [lia| exact I]]. }
  assert (CC2 : client_consts m2) by (apply (cc_agree m1 m2 CC1); apply T12; intros x Hx; cbv beta in Hx; rewrite SHP; lia).
  assert (SS2 : vx_statsh m2) by (apply (vx_statsh_agree m1 m2 SS1); apply T12; intros x Hx; cbv beta in Hx; rewrite SHP; ul).
  assert (SK2 : ro_cells bsegs m2 (usp / 8 + 2147450878) [C1 z8]).
  { eapply ro_cells_agree; [exact SK1|]. apply T12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite SHP. ul. }
  assert (VEC2 : rw_cells bsegs m2 AEX_VEC_OBJ [C8 (wz A8); C8 (wz A8); C8 (wz (A8 + 8))]).
  { eapply rw_cells_agree_nw; [exact VEC1|]. apply T12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold AEX_VEC_OBJ in Hx. rewrite SHP. ul. }
  assert (F16b : rw_cells bsegs m2 (usp - 16) [C8 (wz AEX_VEC_OBJ); C8 ra]).
  { eapply rw_cells_agree_nw; [exact F16a|]. apply T12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite SHP. ul. }
  assert (F64b : rw_cells bsegs m2 (usp - 64) [C8 (wz (usp - 16)); C8 (wz 0xbec14)]).
  { eapply rw_cells_agree_nw; [exact F64a|]. apply T12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite SHP. ul. }

  eapply evt_cut; [eapply (vx_walk2 usp lo A8 ra gp _ u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                             ST2 ltac:(lia) GLO SPH SP16 P0 ltac:(ul) CC2 SS2 SK2 VEC2 F16b F64b MI2)|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & ST3 & F64c).
  assert (T13 : forall P : Z -> Prop, (forall x, P x -> (x + 1 <= usp - 2256 \/ usp - 48 <= x) /\ x <> shad A8) -> agree_on P m1 m3).
  { intros P HP a Ha. rewrite (MU3 a) by (cbn [outside]; pose proof (HP _ Ha); lia). apply MUP. cbn [outside]. pose proof (HP _ Ha). split; [lia| split; [lia| exact I]]. }
  assert (IX3 : ix4 m3) by (apply (ix4_agree m1 m3 (conj GF (conj FD (conj GV VV)))); apply T13; intros x Hx; cbv beta in Hx; rewrite SHP; lia).
  destruct IX3 as (GF3 & FD3 & GV3 & VV3).
  assert (PS3 : ps_cells m3) by (apply (ps_agree m1 m3 PS1); apply T13; intros x Hx; cbv beta in Hx; rewrite SHP; lia).
  assert (SH3 : rw_cells bsegs m3 (shad A8) [CB 1 [Z_to_bv 8 252]]).
  { eapply rw_cells_agree_nw; [exact SH2|]. intros a Ha. apply MU3. cbn [outside cells_size csize Nat.add length] in *. rewrite SHP in Ha. split; [ul| exact I]. }

  eapply evt_cut; [eapply (annot_unpoison8A (usp - 64) lo A8 (wz 0xbede8) gp _ u0 u1 u2 (wz (usp - 16)) (wz SHB) (wz 1) (wz 0) (wz 882690) b7
                             (wz (usp / 8 + 2147450878)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 [Z_to_bv 8 252] F fc m3
                             ST3 ltac:(unfold ANNOT_FRAME; lia) ltac:(unfold kHighShadowEnd; ul) ltac:(lia) P0 A16 LVM ltac:(ul) GF3 FD3 GV3 VV3 PS3 SH3 MI3)|].
  cbv beta. intros ms4 (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & -> & MUU & WMU & MI4 & ST4 & SH4).
  unfold ANNOT_FRAME in MUU. rewrite (ret_pc_even 0xbede8) by lia.
  assert (T14 : forall P : Z -> Prop, (forall x, P x -> (x + 1 <= usp - 2256 \/ usp - 48 <= x) /\ x <> shad A8) -> agree_on P m1 m4).
  { intros P HP a Ha. rewrite (MUU a) by (cbn [outside]; pose proof (HP _ Ha); lia). exact (T13 P HP a Ha). }
  assert (CC4 : client_consts m4) by (apply (cc_agree m1 m4 CC1); apply T14; intros x Hx; cbv beta in Hx; rewrite SHP; lia).
  assert (SS4 : vx_statsh m4) by (apply (vx_statsh_agree m1 m4 SS1); apply T14; intros x Hx; cbv beta in Hx; rewrite SHP; ul).
  assert (SK4 : ro_cells bsegs m4 (usp / 8 + 2147450878) [C1 z8]).
  { eapply ro_cells_agree; [exact SK1|]. apply T14. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite SHP. ul. }
  assert (VEC4 : rw_cells bsegs m4 AEX_VEC_OBJ [C8 (wz A8); C8 (wz A8); C8 (wz (A8 + 8))]).
  { eapply rw_cells_agree_nw; [exact VEC1|]. apply T14. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold AEX_VEC_OBJ in Hx. rewrite SHP. ul. }
  assert (F16d : rw_cells bsegs m4 (usp - 16) [C8 (wz AEX_VEC_OBJ); C8 ra]).
  { eapply rw_cells_agree_nw; [exact F16a|]. apply T14. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite SHP. ul. }
  assert (F48d : rw_cells bsegs m4 (usp - 48) [C8 s2; C8 s1; C8 s0; C8 (wz 0xb4c64)]).
  { eapply rw_cells_agree_nw; [exact F48a|]. apply T14. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite SHP. ul. }
  assert (F64d : rw_cells bsegs m4 (usp - 64) [C8 (wz (usp - 16)); C8 (wz 0xbec30)]).
  { eapply rw_cells_agree_nw; [exact F64c|]. intros a Ha. apply MUU. cbn [outside cells_size csize Nat.add] in *. rewrite SHP. split; [lia| split; [ul| exact I]]. }

  eapply evt_cut; [eapply (vx_walk3 usp lo A8 ra gp _ v0 v1 v2 s0 s1 c0 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F fc m4
                             ST4 ltac:(lia) GLO SPH SP16 P0 ltac:(ul) CC4 SS4 SK4 VEC4 F16d F48d F64d MI4)|].
  cbv beta. intros ms5 (e2 & -> & ST5). apply evt_done.

  pose proof (raw_byte_of_rw1 m1 (shad A8) z8 ltac:(rewrite SHP; unfold img_hull_hi; lia) ltac:(rewrite SHP; ul) SH1) as RAW1.
  pose proof (raw_byte_of_rw1 m4 (shad A8) (Z_to_bv 8 0) ltac:(rewrite SHP; unfold img_hull_hi; lia) ltac:(rewrite SHP; ul) SH4) as RAW4.
  assert (WM04 : wmono bsegs m m4) by (exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WMP (wmono_trans _ _ _ _ WM3 WMU)))).
  assert (AG04 : forall a : word, (bv_unsigned a + 1 <= usp - 2256 \/ usp <= bv_unsigned a) -> ~ (AEX_VEC_OBJ + 8 <= bv_unsigned a < AEX_VEC_OBJ + 16) -> m4 a = m a).
  { intros a H1 H2. destruct (Z.eq_dec (bv_unsigned a) (shad A8)) as [E|NE].
    - replace a with (wa (shad A8)) by (unfold wa; rewrite <- E; apply Z_to_bv_bv_unsigned). rewrite RAW4.
      rewrite <- (MU1 (wa (shad A8))); [symmetry; exact RAW1|].
      unfold wa. rewrite unsigned_lit by (rewrite SHP; ul). cbn [outside]. rewrite SHP. unfold AEX_VEC_OBJ. split; [ul| split; [lia| exact I]].
    - rewrite (T14 (fun x => x = bv_unsigned a)); [| intros x ->; split; [lia| exact NE]| reflexivity]. apply MU1. cbn [outside]. split; [lia| split; [lia| exact I]]. }
  assert (ART4 : ART RT Σ m4).
  { apply (art_client_write RT AF Σ m m4 (usp - 2256) ART0 ltac:(ul)); [| exact WM04].
    intros a Ha. apply AG04.
    - destruct (Z.le_gt_cases (usp - 2256) (bv_unsigned a)); [| left; lia]. right. destruct (Z.le_gt_cases usp (bv_unsigned a)); [lia|].
      exfalso. apply Ha. left. ul.
    - intros Hin. apply Ha. right; left. apply client_static_intro. unfold AEX_VEC_OBJ in Hin. lia. }

  assert (EU16 : bv_unsigned (Z_to_bv 64 (usp - 16)) = usp - 16) by (apply unsigned_lit; lia).
  eapply (aevt_opdel RT AF RC PMc FDO MST Σ K _ _ gp _ _ _ _ s0 s1 _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 A8 8 lo HIN eq_refl ART4 MI4).
  { unfold call_ok. rewrite EU16. split; [exact ST5|]. split; [lia|]. split; [ul|]. split; [ul| clear - SP16; subst usp; Z.div_mod_to_equations; lia]. }
  { unfold unwind_ok. rewrite EU16. left. subst usp. lia. }
  intros Σ1 v w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F1 m5 (ART5 & MI5 & ST6) PRES5 LV1 FRS1 SP1 CR1. rewrite EU16 in ST6, PRES5.
  rewrite (ret_pc_even 0xb4c64) by lia.
  assert (F16e : rw_cells bsegs m5 (usp - 16) [C8 (wz AEX_VEC_OBJ); C8 ra]).
  { eapply rw_cells_agree_nw; [exact F16d|]. apply (agree_of_pres _ _ _ _ _ _ PRES5). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (vx_walk4 usp lo ra gp _ w0 w1 w2 s0 s1 v d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F1 fc m5 ST6 ltac:(lia) GLO SPH F16e MI5)|].
  cbv beta. intros ms6 (-> & ST7). apply evt_done.
  apply (HK Σ1 w0 w1 w2 v d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F1 m5).
  - exact (conj ART5 (conj MI5 ST7)).
  - intros a Ha Ho. cbn [outside VECX_W] in Ho. rewrite (PRES5 a) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]).
    rewrite <- FRS1 in Ha. pose proof (SPLIT Σ1 m5 _ ART5 SP1 Ha). apply AG04; [lia| unfold AEX_VEC_OBJ in *; lia].
  - eapply rw_cells_agree_nw; [exact VEC4|]. apply (agree_of_pres _ _ _ _ _ _ PRES5). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    right; left. apply client_static_intro. unfold AEX_VEC_OBJ in Hx. lia.
  - exact LV1. - exact FRS1. - exact SP1. - exact CR1.
Qed.
End VX.
