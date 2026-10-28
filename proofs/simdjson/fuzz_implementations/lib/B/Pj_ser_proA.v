(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface I_lkit
     FX_lib Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma land_m32d : forall x, 0 <= x < 2^64 -> x mod 16 = 0 ->
  exists dd, (dd = 0 \/ dd = 16) /\ Z.land x 18446744073709551584 = x - dd /\ (x - dd) mod 32 = 0.
Proof.
  intros x Hx X16. exists (x - 32 * (x / 32)). rewrite (land_m32 x Hx).
  split; [Z.div_mod_to_equations; lia|]. split; [lia| Z.div_mod_to_equations; lia].
Qed.

Definition sa_savedA (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ser_pro1 : forall (q lo SB DOC i : Z) (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo q -> lo + 432 <= q -> 0x6e1000 <= lo -> q + 16 <= USTACK_TOP -> q mod 16 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (dd : Z) (a1' a2' : word),
      (dd = 0 \/ dd = 16) /\ (q - 416 - dd) mod 32 = 0 /\
      ms = MS (mkR (wz 0xb7f28) (wz (q - 416 - dd)) gp (wz TPV_A) t0 t1 t2 (wz q) (wz (q - 416 - dd)) (wz 352) a1' a2' a3 a4 a5 a6 a7
                   s2 s3 s4 s5 (wz i) s7 (wz SB) (wz 2147450880) s10 (wz DOC) t3 t4 t5 t6) F (wz (e_stack_malloc 3)) fc None m1 (seg_rom bsegs)
      /\ munch [(q - 416, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo (q - 104) /\ rw_cells bsegs m1 (q - 104) (sa_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz SB) (wz DOC) (wz i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PJ_APPEND_ELEM_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO QT Q16 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold PJ_APPEND_ELEM_A, e_stack_malloc, TPV_A, USTACK_TOP, sa_savedA in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 416, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

  zstep.
  carve_frame 416%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 416 _ [] [8; 304; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.

  lstep. do 13 zstep. zstep. zstep.
  destruct (land_m32d (q + -416) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (dd & DD & ELAND & B32). rewrite ELAND.

  do 7 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  pose proof (stk_of_rw_cells bsegs _ _ _ FRl) as STl. cbn [cells_size csize Nat.add] in STl.
  pose proof (stk_merge bsegs _ _ _ _ ST STl ltac:(lia)) as ST2.
  replace (q + -416 + Z.of_nat 312) with (q - 104) in FRs, ST2 by lia.
  replace (q + -416 - dd) with (q - 416 - dd) by lia. replace (q + -416 + 416) with q by lia.
  apply evt_done. eexists. exists dd. eexists. eexists. split; [exact DD|]. split; [lia|]. split; [cbv delta [mkR]; reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx |- *. lia. }
  split; [exact WM|]. split; [eassumption|]. split; [exact ST2| exact FRs].
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Definition c8c (c : cell) : cell := match c with CB n bs => if Nat.eqb n 8 then C8 (le_bytes_to_word bs) else c | _ => c end.
Lemma c8ify_ok : forall cs, cells_wf cs ->
  cells_wf (map c8c cs) /\ cells_bytes (map c8c cs) = cells_bytes cs /\ cells_size (map c8c cs) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; intros Hwf; [repeat split; reflexivity|].
  destruct Hwf as [Hc Hcs]. destruct (IH Hcs) as (W & B & S).
  destruct c as [v|v|v|b|n bs]; cbn [map c8c cells_wf cells_bytes cells_size]; try (rewrite B, S; repeat split; auto; fail).
  destruct (Nat.eqb_spec n 8) as [->|NE]; cbn [cells_wf cells_bytes cells_size cbytes csize cell_wf]; rewrite B, S.
  - cbn in Hc. rewrite (le8_of_bytes bs Hc). repeat split; auto.
  - repeat split; auto.
Qed.
Lemma rw_cells_c8ify : forall (m : mem) A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A (map c8c cs).
Proof.
  intros m A cs [[Hwf Hb] Hw]. destruct (c8ify_ok cs Hwf) as (W & B & S).
  split; [split; [exact W| rewrite B; exact Hb]| rewrite S; exact Hw].
Qed.

Definition ser_frame_raw (f SB DOC : Z) (w : wkA) (x : xjA) : list cell :=
  [C8 (xj0 x); C8 (xj8 x); C8 (xj16 x); C8 (xj24 x); C8 (lnotw (f + 304)); C8 (wz (f + 241)); C8 (lnotw (f + 241));
   C8 (wz (f + 32)); C8 (wz (f + 176)); C8 (wz (f + 112)); C8 (xj80 x); C8 (wz 1); C8 (wz 1); C8 (wz f);
   C8 (wz DOC); C8 (wz (DOC + 8)); C8 (wz (f + 304)); C8 (wz (f + 273)); C8 (lnotw (f + 273)); C8 (wz MASK56);
   C8 (wz f); C8 (w168 w); C8 (w176 w); C8 (w184 w); C8 (wz SB); C8 (wz (f / 8 + 2147450880)); C8 (xj208 x); C8 (xj216 x);
   C8 (w224 w); C8 (wz (SB + 64)); C8 (wz (SB + 80)); C8 (w248 w); C8 (w256 w); C8 (w264 w); C8 (wz END93); C8 (wz TOPMASK);
   C8 (xj288 x); C8 (xj296 x); C8 (wz f)].
Lemma ser_frame_raw_eq : forall E I w x, ser_frameA E I w x = ser_frame_raw (si_f I) (pa_SB E) (pa_DOC E) w x.
Proof. intros. reflexivity. Qed.

Definition ser_shpatN : list byte :=
  map (Z_to_bv 8) [-15; -15; -15; -15; -8; -8; -8; -8; -8; -14; -14; -14; -14; -14; -8; -8; -8; -14; -14; -14; -14; -14;
                   -8; -8; -8; -14; -14; -14; -14; -14; -8; -14; -14; -14; -8; -14; -14; -14; 0; 0; -13; -13; -13; -13].
Lemma ser_shpatN_eq : ser_shpatN = ser_shpatA.
Proof.
  unfold ser_shpatN, ser_shpatA, ser_shpatZ. cbn [map].
  repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity.
Qed.

Lemma ser_pro2 : forall (q b f lo SB DOC i : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s10 t3 t4 t5 t6 : word)
    (h sh t iso : list byte) F fc (m : mem),
  0 < f -> f + 512 <= lo -> f / 8 + 2147450880 + 64 <= lo -> 8 * (f / 8) = f ->
  (f + 512 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 64 <= f) ->
  0x6e1000 <= lo -> lo <= b -> b + 416 <= q -> q + 16 <= USTACK_TOP -> 0 <= SB -> SB + 96 <= lo -> 0 < DOC -> DOC + 24 <= lo -> DOC mod 8 = 0 -> 0 <= i < 2^32 ->
  stk bsegs m b (q - 104) ->
  rw_cells bsegs m f [CB 24 h] -> stk bsegs m (f + 24) (f + 304) -> u8arr bsegs m (f + 304) iso -> length iso = 16%nat ->
  rw_cells bsegs m (f / 8 + 2147450880) [CB 64 sh] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (x : xjA) (w : wkA) (ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' : word),
      ms = MS (mkR ra' (wz b) gp (wz TPV_A) t0' t1' t2' (wz q) (wz b) a0' (wz 0) a2' a3' a4' a5' a6' a7'
                   (wz (SB + 72)) s3' (wz (SB + 64)) (wz (f / 8 + 2147450880)) (wz i) (wz (SB + 80)) (wz SB) (wz 2147450880) (wz 0) (wz DOC) t3' t4' t5' t6')
              F (wz PJ_HEAD_A) fc None m1 (seg_rom bsegs)
      /\ munch [(b, b + 312); (f, f + 24); (f + 304, f + 305); (f / 8 + 2147450880, f / 8 + 2147450924)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 b (ser_frame_raw f SB DOC w x) /\ stk bsegs m1 (b + 312) (q - 104)
      /\ rw_cells bsegs m1 f [C8 (wz 1102416563); C8 (wz 0x22f0b); C8 (wz 0xb7eb0)] /\ stk bsegs m1 (f + 24) (f + 304)
      /\ u8arr bsegs m1 (f + 304) (upd iso 0 (Z_to_bv 8 0))
      /\ exists t20, rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 ser_shpatA ++ [CB 20 t20]))
    (MS (mkR (wz 0xb7f28) (wz b) gp (wz TPV_A) t0 t1 t2 (wz q) (wz b) (wz f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz i) s7 (wz SB) (wz 2147450880) s10 (wz DOC) t3 t4 t5 t6)
        F (wz 0xb7f28) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO SFL Ef SHf GLO LOB BQ QT SB0 SBR DOC0 DOCR D8 IR STF FH F3S IS ISL SHC MI.
  unfold PJ_HEAD_A, TPV_A, USTACK_TOP in *.
  pose proof (munch_refl [(b, b + 312); (f, f + 24); (f + 304, f + 305); (f / 8 + 2147450880, f / 8 + 2147450924)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  destruct (stk_split bsegs m _ (b + 312) _ STF ltac:(lia)) as [STl GAP].
  destruct (stk_CB bsegs m _ _ STl ltac:(lia)) as (jf & FR). replace (Z.to_nat (b + 312 - b)) with 312%nat in FR by lia.
  apply (rw_cells_split_CB bsegs _ _ [] 312 _ [] [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "j" in set (j := tt) in FR; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH; [| reflexivity]. cbn [mk_CB_cells app] in FH.
  repeat match type of FH with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "h" in set (j := tt) in FH; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 64 _ []
           [1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1;1;1;1;1;1;1; 1;1;1;1; 20]%nat) in SHC; [| reflexivity].
  cbn [mk_CB_cells app] in SHC.
  repeat match type of SHC with context [CB 1 ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "z" in set (j := tt) in SHC; clearbody j end.
  assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  assert (ED7 : Z.land DOC 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; exact D8).

  step. zstep. step. if_cases K0; zify_cond K0; [clear K0| exfalso; pjnorm_in K0; lia].

  ls. zstep. zstep. zstep. ls. do 3 (zstep; ls).

  zstep. zstep. zstep. zstep. zstep. pjnorm. zstep. zstep. zstep. zstep.

  do 6 zstep.

  zstep. rewrite ED7. zstep. replace (0 <? DOC) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. zstep. ls.

  zstep. zstep. ls. zstep. ls. ls. zstep.

  do 34 ls.

  zstep. ls. zstep. ls. zstep. cbn [Z.eqb Z.b2z].

  do 10 ls. ls.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_store_ok bsegs mm (f + 304) iso 0 (wa (f + 304 + 0)) IS ltac:(rewrite ISL; lia) eq_refl) as SOK1 end.
  step. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa _) _) =>
    pose proof (u8arr_write bsegs mm (f + 304) iso 0 (Z_to_bv 8 0) IS ltac:(rewrite ISL; lia)) as IS';
    replace (wa (f + 304 + 0)) with aa in IS' by (unfold wa; f_equal; lia) end.
  change (Z.to_nat 0) with 0%nat in IS'. store_done. try clear IS.

  ls. zstep. ls. zstep. ls.

  zstep. rewrite lnot_mod64 by lia. ls. ls. zstep. rewrite lnot_mod64 by lia. ls. ls. zstep. rewrite lnot_mod64 by lia. ls.

  zstep. ls. ls. ls. ls. ls. ls.
  apply rw_cells_c8ify in FR. cbn [map c8c Nat.eqb] in FR.
  apply evt_done.
  eexists. eexists (mkXJ _ _ _ _ _ _ _ _ _). eexists (mkWK _ _ _ _ _ _ _). do 16 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact FR|]. split; [exact GAP|]. split; [exact FH|]. split; [exact F3S|]. split; [exact IS'|].
  rewrite <- ser_shpatN_eq. eexists. unfold ser_shpatN. cbn [map app]. exact SHC.
Qed.
