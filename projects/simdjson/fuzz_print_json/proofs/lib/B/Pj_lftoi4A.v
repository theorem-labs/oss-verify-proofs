(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_pidiA Pj_lftoi1A Pj_lftoi2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition pj_shadow_x : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 10 ++ repeat (Z_to_bv 8 (-14)) 4
  ++ repeat (Z_to_bv 8 (-8)) 36 ++ repeat (Z_to_bv 8 (-13)) 10.
Definition pj_shadow2 (t : list byte) : list cell := map C1 pj_shadow_x ++ [CB 48 t].

Lemma pj_shadow_bytes_length : length pj_shadow_bytes = 80%nat.
Proof. reflexivity. Qed.
Lemma pj_shadow_x_length : length pj_shadow_x = 80%nat.
Proof. reflexivity. Qed.

Lemma pj_walkG_err : forall (usp sp' f d n : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word) (r : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= sp' -> sp' + 88 < 2^63 -> 1 <= bv_unsigned r < 64 ->
  rw_cells bsegs m (sp' + 64) (res_cellsA (f + 184) r j20) -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs e_pdtor (Z_to_bv 64 0xb1ad8) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 160)) (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m))
    (lf_regs 0xb1888 x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RR RC MI. unfold lf_regs, e_pdtor, res_cellsA in *.
  assert (NZ : bv_eqb r (Z_to_bv 64 0) = false).
  { destruct (bv_eqb r (Z_to_bv 64 0)) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. subst r. rewrite unsigned_lit in RR by lia. lia. }
  rewrite NZ in RC.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [C4 r; CB 4 j20] [16]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
  assert (ER : r = Z_to_bv 64 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ER in RC.
  zstep. rewrite ER. rewrite sx32_small by lia. zstep. zstep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|]. clear G.
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pj_walkG_ok : forall (usp sp' f d n : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= sp' -> sp' + 88 < 2^63 ->
  rw_cells bsegs m (sp' + 64) (res_cellsA (f + 184) (Z_to_bv 64 0) j20) -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs 0xb1898 x1 sp' gp tp t0 t1 t2 usp (Z_to_bv 64 0) (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m))
    (lf_regs 0xb1888 x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RC MI. unfold lf_regs, res_cellsA in *.
  rewrite bv_eqb_refl in RC.
  zstep. rewrite sx32_small by lia. zstep. zstep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|]. clear G.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pj_walkJ : forall (usp sp' f d n : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 ->
  evt bsegs (eq (lf_regs e_pdtor (Z_to_bv 64 0xb1ad8) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 160)) a1 a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m))
    (lf_regs 0xb1ad0 x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH. unfold lf_regs, e_pdtor in *.
  zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pj_walkX1 : forall (usp sp' f lo d n : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word) (h3 t : list byte) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> f / 8 + 2147450880 + 128 <= lo -> 0 <= f / 8 ->
  (f + 1024 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= f) -> lo < 2^63 ->
  rw_cells bsegs m f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x13300)) (C8 (Z_to_bv 64 0xb15fc)) h3) -> rw_cells bsegs m (f / 8 + 2147450880) (pj_shadow1 t) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = lf_regs (e_set_shadow 245) (Z_to_bv 64 0xb1b20) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 128) a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m'
      /\ munch [(f, f + 8); (f / 8 + 2147450880 + 20, f / 8 + 2147450880 + 30)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' f (fz_hdr (C8 (Z_to_bv 64 0x45e0360e)) (C8 (Z_to_bv 64 0x13300)) (C8 (Z_to_bv 64 0xb15fc)) h3)
      /\ rw_cells bsegs m' (f / 8 + 2147450880) (pj_shadow2 t))
    (lf_regs 0xb1ad8 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LOH FH FS MI.
  unfold lf_regs, fz_hdr, pj_shadow1, pj_shadow2, pj_shadow_bytes, pj_shadow_x, e_set_shadow in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880 + 20, f / 8 + 2147450880 + 30)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. do 10 ls.
  zstep. zstep. ls.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; eassumption.
Qed.

Lemma pj_walkX2 : forall (usp sp' f fl lo d n : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 1024 <= lo -> 0 < fl -> fl + 1 <= lo ->
  0x6d6000 <= lo -> lo <= sp' -> cells_size LC = 88%nat -> sp' + 88 <= usp - 104 -> usp < 2^63 ->
  stk bsegs m lo sp' -> rw_cells bsegs m sp' LC -> stk bsegs m (sp' + 88) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 1016) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st xra (Z_to_bv 64 usp) gp tp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (lf_regs 0xb1b20 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f n d s7 s8 s9 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold lf_regs, fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.
  zstep. do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 88%nat) with 88 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
