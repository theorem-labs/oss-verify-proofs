(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zvm Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpo Z4a Z6y Z45 Z4e Z4l Z4m Z4n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition ATPA_GETSTR : Z := 0x97804.

Definition fa_shadow3 (t : list byte) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 3 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 10 ++ repeat (Z_to_bv 8 (-13)) 6)
  ++ [CB 4 t].

Lemma code_lw : forall (code : Z), 0 <= code < 64 -> bv_unsigned (Z_to_bv 64 code) = code.
Proof. intros code H. apply unsigned_lit. lia. Qed.

Lemma fa_walk11 : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (r : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 -> 1 <= bv_unsigned r < 64 ->
  rw_cells bsegs m (sp' + 136) (res_cellsA (f + 120) r j20) -> mem_inv bsegs m ->
  evt bsegs (eq (sa_regs e_pdtor (Z_to_bv 64 0x96e80) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 96)) (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96dcc x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RR RC MI. unfold sa_regs, e_pdtor, res_cellsA in *.
  assert (NZ : bv_eqb r (Z_to_bv 64 0) = false).
  { destruct (bv_eqb r (Z_to_bv 64 0)) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. subst r. rewrite unsigned_lit in RR by lia. lia. }
  rewrite NZ in RC.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [C4 r; CB 4 j20] [16]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
  assert (ER : r = Z_to_bv 64 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ER in RC.
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ER in K0; try rewrite a_sx32_small in K0 by lia; try rewrite unsigned_lit in K0 by lia; lia|].
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ER in K; try rewrite a_sx32_small in K by lia; try rewrite unsigned_lit in K by lia; lia].
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk11c : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (r0 : word) (j code : Z) (jn : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 -> 1 <= code < 64 ->
  rw_cells bsegs m (sp' + 96) [C8 r0; C8 (Z_to_bv 64 j); C4 (Z_to_bv 64 code); CB 4 jn] -> mem_inv bsegs m ->
  evt bsegs (eq (sa_regs e_pdtor (Z_to_bv 64 0x96e80) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 96)) (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96e40 x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH CR RC MI. unfold sa_regs, e_pdtor in *.
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; try rewrite a_sx32_small in K0 by lia; try rewrite unsigned_lit in K0 by lia; lia|].
  zstep. if_cases K; zify_cond K; [| exfalso; try rewrite a_sx32_small in K by lia; try rewrite unsigned_lit in K by lia; lia].
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk11g : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (b16 : list byte) (code : Z) (jn : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 -> 0 <= code < 64 ->
  rw_cells bsegs m (sp' + 56) [CB 16 b16; C4 (Z_to_bv 64 code); CB 4 jn] -> mem_inv bsegs m ->
  evt bsegs (eq (sa_regs e_pdtor (Z_to_bv 64 0x96e80) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 96)) (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96e6c x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH CR RC MI. unfold sa_regs, e_pdtor in *.
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; try rewrite a_sx32_small in K0 by lia; try rewrite unsigned_lit in K0 by lia; lia|].
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk12 : forall (usp sp' f : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (t jr : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= f / 8 -> f / 8 + 2147450880 + 32 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 ->
  (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) -> (sp' + 184 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= sp') ->
  rw_cells bsegs m (f / 8 + 2147450880) (fa_shadow2 t) -> rw_cells bsegs m (sp' + 136) [CB 24 jr] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (jr' : list byte),
      ms = MS (mkR (Z_to_bv 64 0x96eb8) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (sp' + 136)) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
                   (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
              F (Z_to_bv 64 ATPA_DESTROY) fc None m1 (seg_rom bsegs)
      /\ munch [(f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22); (sp' + 136, sp' + 144)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (fa_shadow1 t)
      /\ rw_cells bsegs m1 (sp' + 136) [C8 (Z_to_bv 64 (f + 32)); CB 16 jr'])
    (sa_regs 0x96e80 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH FD SH SP0 SPH SEP SEP2 FS RC MI.
  unfold sa_regs, ATPA_DESTROY, fa_shadow2, fa_shadow1 in *. cbn [map app repeat] in *.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 16]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
  set (jr' := firstn 16 (skipn 8 jr)) in RC. clearbody jr'.
  pose proof (munch_refl [(f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22); (sp' + 136, sp' + 144)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. do 10 ls.
  ls. zstep. zstep.
  apply evt_done. eexists. exists jr'. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; eassumption.
Qed.

Definition sx_regs (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s6 s7 s8 : word) (t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
          (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma fa_walk13a : forall (usp sp' f lo : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) (h3 t : list byte) F fc (m : mem),
  0 < f -> f + 256 <= lo -> f / 8 + 2147450880 + 32 <= lo -> 0 <= f / 8 ->
  (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) -> lo <= sp' -> sp' + 184 < 2^63 ->
  rw_cells bsegs m f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e816)) (C8 (Z_to_bv 64 0x96ab0)) h3) -> rw_cells bsegs m (f / 8 + 2147450880) (fa_shadow1 t) ->
  rw_cells bsegs m (sp' + 24) [C8 (Z_to_bv 64 f)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a0' : word),
      ms = sx_regs 0x96f5c ra sp' gp tp t0 t1 t2 usp a0' (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m'
      /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
    (sx_regs 0x96eb8 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LSP SPH FH FS FL MI.
  unfold sx_regs, fz_hdr, fa_shadow1 in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  do 3 ls.
  zstep. zstep. ls.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. do 32 ls.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM| eassumption].
Qed.

Lemma fa_walk13b : forall (usp sp' f fl lo : Z) (ra gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 256 <= lo -> 0 < fl -> fl + 1 <= lo ->
  0x676000 <= lo -> lo <= sp' -> cells_size LC = 184%nat -> sp' + 184 <= usp - 104 -> usp < 2^63 ->
  stk bsegs m lo sp' -> rw_cells bsegs m sp' LC -> stk bsegs m (sp' + 184) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st xra (Z_to_bv 64 usp) gp tp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (sx_regs 0x96f5c ra sp' gp tp t0 t1 t2 usp a0 (Z_to_bv 64 f) a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold sx_regs, fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.
  zstep. do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 184%nat) with 184 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.

Lemma fa_walkR1 : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 ->
  rw_cells bsegs m (sp' + 136) [C8 (Z_to_bv 64 (f + 120)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20] -> mem_inv bsegs m ->
  evt bsegs (eq (sa_regs e_asan_memcpy (Z_to_bv 64 0x96dec) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (sp' + 120)) (Z_to_bv 64 (sp' + 136)) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                      f s2 s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96dcc x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RC MI. unfold sa_regs, e_asan_memcpy in *.
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. zstep. zstep. if_false.
  zstep. if_false.
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walkR2 : forall (usp sp' f A : Z) (p0 l0 p1 l1 : Z) (rest : list cell) (c1 c2 : cell)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 ->
  0 < A -> A mod 8 = 0 -> A + 32 < 2^63 -> 0 <= p1 < 2^64 -> 0 <= l1 < 2^64 -> 0 <= p0 < 2^64 -> 0 <= l0 < 2^64 ->
  rw_cells bsegs m (f + 32) (C8 (Z_to_bv 64 A) :: c1 :: c2 :: []) ->
  rw_cells bsegs m A (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: C8 (Z_to_bv 64 p1) :: C8 (Z_to_bv 64 l1) :: rest) ->
  shz m A 32 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists a4' a5' : word,
               ms = lvl_entry ATP_ELEM_A (Z_to_bv 64 0x96e40) sp' gp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (sp' + 96) (sp' + 120) p1 l1 a4' a5' a6 a7
                      s2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
                      (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc m)
    (sa_regs 0x96dec x1 sp' gp (Z_to_bv 64 TPV) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH A0 A8 AH P1R L1R P0R L0R SV EL SHZA MI.
  unfold sa_regs, lvl_entry, ATP_ELEM_A, TPV in *.
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).

  zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
  zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].

  astep. zstep. replace (Z.land (A + 16) 7) with 0 by (rewrite Z.land_ones with (n := 3) by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  zstep. if_cases K2; zify_cond K2; [exfalso; lia|].

  chk0 SHZA (A + 16). zstep. if_false.

  astep. chk0 SHZA (A + 24). zstep. if_false.

  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walkR3 : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (r0 : word) (j : Z) (jn : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 ->
  rw_cells bsegs m (sp' + 96) [C8 r0; C8 (Z_to_bv 64 j); C4 (Z_to_bv 64 0); CB 4 jn] -> mem_inv bsegs m ->
  evt bsegs (eq (sa_regs e_asan_memcpy (Z_to_bv 64 0x96e60) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (sp' + 80)) (Z_to_bv 64 (sp' + 96)) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                      f s2 s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96e40 x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RC MI. unfold sa_regs, e_asan_memcpy in *.
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. zstep. zstep. if_false.
  zstep. if_false.
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walkR4 : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 184 < 2^63 ->
  evt bsegs (eq (sa_regs ATPA_GETSTR (Z_to_bv 64 0x96e6c) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (sp' + 56)) (Z_to_bv 64 (sp' + 80)) a2 a3 a4 a5 a6 a7
                      f s2 s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96e60 x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH. unfold sa_regs, ATPA_GETSTR in *.
  zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
