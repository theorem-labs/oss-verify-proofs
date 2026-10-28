(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition f5x16 : list byte := repeat (Z_to_bv 8 (-11)) 16.

Lemma pad_exit1 : forall (S sp2 f lo OS N BUF : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h0 : word) (sh : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length sh = 12%nat -> length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 <= OS -> OS + 288 <= lo -> (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  lo <= sp2 -> sp2 + 40 < 2^63 -> 0 <= N < 2^64 -> 0 <= BUF < 2^64 ->
  shz m OS 288 ->
  rw_cells bsegs m (sp2 + 24) [C8 (wz ((OS + 160) / 8 + 2147450880)); C8 (wz (OS + 160))] -> rw_cells bsegs m (OS + 160) [C8 (wz 0)] ->
  rw_cells bsegs m f [C8 h0] -> rw_cells bsegs m (f / 8 + 2147450880) (map C1 sh ++ map (fun l => CB 1 l) ls4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (-11)) a1 a2 a3 a4 a5 a6 a7
                   (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xbe898) fc None m1 (seg_rom bsegs)
      /\ munch [(OS + 160, OS + 168); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (OS + 160) [C8 (wz 0)] /\ rw_cells bsegs m1 f [C8 (wz 0x45e0360e)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 f5x16))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz OS) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xbe7fc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS LS4 F0 FLO FD SLO SEP O0 OLO OF OSH LSP SPH NR BR SHZ0 L0 WID FH FS MI.
  do 12 (destruct sh as [|? sh]; [discriminate LS|]). destruct sh; [| discriminate LS]. clear LS.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold f5x16 in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(OS + 160, OS + 168); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 160)) = OS + 160) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ES24 : bv_unsigned (Z_to_bv 64 (sp2 + 24)) = sp2 + 24) by (apply unsigned_lit; lia).
  zstep.
  shz_pose SHZ0 (OS + 160). zstep. shz_norm. zstep. if_false.
  zstep.
  lstep.
  zstep.
  zstep. zstep. lstep.
  zstep. if_cases K'; zify_cond K'; [exfalso; lia|].
  zstep.
  do 16 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma pad_exit2 : forall (S sp2 f fl lo OS : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= OS -> OS + 288 <= lo ->
  0x6e0000 <= lo -> lo <= sp2 -> cells_size LC = 88%nat -> sp2 + 88 <= S - 104 -> S < 2^63 ->
  stk bsegs m lo sp2 -> rw_cells bsegs m sp2 LC -> stk bsegs m (sp2 + 88) (S - 104) ->
  rw_cells bsegs m (S - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR xra (wz S) gp tp t0 t1 t2 xs0 xs1 (wz OS) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
              F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo S /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz OS) s4 s5 s6 (wz f) s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xbe898) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO FL0 FLLO O0 OLO GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep. zstep.
  replace (S - 104) with (S + -104) in FRs by lia.
  do 13 zstep. zstep.
  replace (S + -104) with (S - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 88%nat) with 88 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (S - 104 + Z.of_nat 104) with S in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.

Lemma op_exit1 : forall (usp sp' f lo OS ivp : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s9 s10 t3 t4 t5 t6 : word)
    (h0 : word) (j7 j148 : list byte) (sh : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length sh = 12%nat -> length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < OS -> OS + 288 <= lo -> (OS + 288 <= f \/ f + 128 <= OS) -> (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= OS) ->
  0x6e0000 <= lo -> lo <= sp' - 16 -> sp' < 2^63 -> 0 <= ivp < 2^64 ->
  stk bsegs m lo sp' -> rw_cells bsegs m (sp' + 56) [C8 (wz f)] ->
  rw_cells bsegs m (f + 64) [C1 (Z_to_bv 8 1); CB 7 j7; C8 (wz (OS + 128))] ->
  rw_cells bsegs m (OS + 128) [C8 (wz PJ_OS_VPTR_A); C8 (wz ivp); CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]; CB 4 j148;
                               C8 (wz 6); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz OS)] ->
  ro_cells bsegs m PJ_NULSB_VT_A [C8 (wz PJ_XSPUTN_A); C8 (wz PJ_OVERFLOW_A); C8 (wz 8)] ->
  rw_cells bsegs m f [C8 h0] -> rw_cells bsegs m (f / 8 + 2147450880) (map C1 sh ++ map (fun l => CB 1 l) ls4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a2' : word) (m1 : mem),
      ms = MS (mkR (wz 0xbe250) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz (-11)) (wz f) a2' a3 a4 a5 a6 a7
                   (wz f) s3 (wz (f + 64)) s5 s6 s7 (wz (f / 8 + 2147450880)) s9 s10 (wz 2147450880) t3 t4 t5 t6)
              F (wz 0xbe2b4) fc None m1 (seg_rom bsegs)
      /\ munch [(sp' - 16, sp'); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo sp' /\ rw_cells bsegs m1 f [C8 (wz 0x45e0360e)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 f5x16))
    (MS (mkR ra (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) s3 (wz (f + 64)) s5 s6 s7 (wz (f / 8 + 2147450880)) s9 s10 (wz 2147450880) t3 t4 t5 t6)
        F (wz 0xbe248) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS LS4 F0 FLO FD SLO SEP O0 OLO OF OSH GLO LSP SPH IVR ST L7 SEN IOS VT FH FS MI.
  do 12 (destruct sh as [|? sh]; [discriminate LS|]). destruct sh; [| discriminate LS]. clear LS.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold f5x16, PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A, PJ_OS_VPTR_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' - 16, sp'); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (E64 : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 128)) = OS + 128) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  zstep. zstep.
  carve_frame 16%nat ST.
  do 3 lstep.
  do 4 zstep.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. if_false.
  zstep. zstep.
  zstep. if_true.
  do 3 zstep.
  release_frame FR ST sp'.
  zstep.
  zstep. ls. ls.
  zstep. zstep. lstep.
  assert (ES56 : bv_unsigned (Z_to_bv 64 (sp' + 56)) = sp' + 56) by (apply unsigned_lit; lia).
  zstep.
  zstep. if_cases K'; zify_cond K'; [exfalso; lia|].
  zstep.
  do 16 ls.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma op_exit2 : forall (usp sp' f fl lo OSP : Z) (ra gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= OSP < 2^64 ->
  0x6e0000 <= lo -> lo <= sp' -> cells_size LC = 88%nat -> sp' + 88 <= usp - 104 -> usp < 2^63 ->
  stk bsegs m lo sp' -> rw_cells bsegs m sp' LC -> stk bsegs m (sp' + 88) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR xra (wz usp) gp tp t0 t1 t2 xs0 xs1 (wz OSP) (wz f) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
              F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') a0 (wz f) a2 a3 a4 a5 a6 a7 s2 (wz OSP) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xbe2b4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO FL0 FLLO OR GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.
  do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 88%nat) with 88 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
