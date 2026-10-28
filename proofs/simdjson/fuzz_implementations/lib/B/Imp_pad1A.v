(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_walk Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_os_put1A Pj_os_put2A Imp_oss_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition pad_mid0I (S lo O BUF N FILL : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 : list byte),
    ms = entry_st (wz 0xbe5c0) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz 96) a1' a2' (wz (BUF + N)) (wz (O + 112)) (wz FILL) a6 a7
                  s2 (wz (O + 8)) (wz SHB) (wz FILL) (wz (O + 112)) s7 (wz BUF) s9 (wz BUF) s11 t3 t4 t5 t6 F fc e_stack_malloc_1 m1
    /\ munch [(S - 192, S)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (S - 192)
    /\ rw_cells bsegs m1 (S - 192) (pad_locals0 j0 j1 j2 j3 j4 j5 j6 (BUF + N) j8 j9 j10)
    /\ stk bsegs m1 (S - 192 + 88) (S - 104)
    /\ rw_cells bsegs m1 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma pad_walk0I : forall (S lo O BUF N FILL : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo S -> lo <= S - 192 -> 0x6e0000 <= lo -> S < 2^63 -> S mod 32 = 0 ->
  0 <= O -> O + 264 < 2^64 -> 0 <= BUF -> BUF + N < 2^64 -> 0 <= N -> 0 <= FILL < 2^64 ->
  client_consts m -> mem_inv bsegs m ->
  evt bsegs (pad_mid0I S lo O BUF N FILL ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (wz S) gp tp t0 t1 t2 s0 s1 (wz (O + 8)) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (O + 112)) (wz FILL) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc OSS_PADOUT_A m).
Proof.
  intros until m. intros ST LO GLO SPH S32 OR OH BR BH NR FR0 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, OSS_PADOUT_A, e_stack_malloc_1, pad_mid0I, fa_saved, pad_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(S - 192, S)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 192%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (S + -192)) by lia.
  replace (32 * ((S + -192) / 32)) with (S + -192) by (Z.div_mod_to_equations; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (S + -192)) = S + -192) by (apply unsigned_lit; lia).
  do 3 zstep. lstep. do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (S + -192 + Z.of_nat 88) with (S - 104) in FRs by lia.
  replace (S + -192) with (S - 192) in * by lia.
  apply evt_done. do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (S - 192 + 88) with (S - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma pad_exit1I : forall (S sp2 f lo O N BUF : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h0 : word) (sh : list byte) (ls4 : list (list byte)) F fc (m : mem),
  length sh = 12%nat -> length ls4 = 4%nat ->
  0 < f -> f + 128 <= lo -> 0 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 <= O -> O + 264 <= lo -> (O + 264 <= f \/ f + 128 <= O) -> (O + 264 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= O) ->
  lo <= sp2 -> sp2 + 40 < 2^63 -> 0 <= N < 2^64 -> 0 <= BUF < 2^64 ->
  shz m O 264 ->
  rw_cells bsegs m (sp2 + 24) [C8 (wz ((O + 136) / 8 + 2147450880)); C8 (wz (O + 136))] -> rw_cells bsegs m (O + 136) [C8 (wz 0)] ->
  rw_cells bsegs m f [C8 h0] -> rw_cells bsegs m (f / 8 + 2147450880) (map C1 sh ++ map (fun l => CB 1 l) ls4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) (wz (-11)) a1 a2 a3 a4 a5 a6 a7
                   (wz f) (wz (O + 8)) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xbe898) fc None m1 (seg_rom bsegs)
      /\ munch [(O + 136, O + 144); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (O + 136) [C8 (wz 0)] /\ rw_cells bsegs m1 f [C8 (wz 0x45e0360e)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 f5x16))
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7
             (wz f) (wz (O + 8)) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xbe7fc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS LS4 F0 FLO FD SLO SEP O0 OLO OF OSH LSP SPH NR BR SHZ0 L0 WID FH FS MI.
  do 12 (destruct sh as [|? sh]; [discriminate LS|]). destruct sh; [| discriminate LS]. clear LS.
  do 4 (destruct ls4 as [|? ls4]; [discriminate LS4|]). destruct ls4; [| discriminate LS4]. clear LS4.
  unfold f5x16 in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(O + 136, O + 144); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp2) = sp2) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (O + 136)) = O + 136) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ES24 : bv_unsigned (Z_to_bv 64 (sp2 + 24)) = sp2 + 24) by (apply unsigned_lit; lia).
  zstep.
  shz_pose SHZ0 (O + 136). zstep. shz_norm. zstep. if_false.
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

Lemma pad_exit2I : forall (S sp2 f fl lo O : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= O -> O + 264 <= lo ->
  0x6e0000 <= lo -> lo <= sp2 -> cells_size LC = 88%nat -> sp2 + 88 <= S - 104 -> S < 2^63 ->
  stk bsegs m lo sp2 -> rw_cells bsegs m sp2 LC -> stk bsegs m (sp2 + 88) (S - 104) ->
  rw_cells bsegs m (S - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR xra (wz S) gp tp t0 t1 t2 xs0 xs1 (wz (O + 8)) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
              F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo S /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (wz sp2) gp tp t0 t1 t2 (wz S) (wz sp2) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz (O + 8)) s4 s5 s6 (wz f) s8 s9 s10 s11 t3 t4 t5 t6)
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

Lemma acc_agreeP : forall (m m' : mem) a n, acc bsegs m a n -> agree_on (fun x => shad a <= x <= shad (a + n)) m m' -> acc bsegs m' a n.
Proof.
  intros m m' a n H AG i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_agree bsegs m m' _ _ Hb). intros x Hx. cbn [length] in Hx. apply AG. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

Lemma cells_size_map_C1p : forall bs : list byte, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.
Lemma cells_size_map_CB1 : forall ls : list (list byte), cells_size (map (fun l => CB 1 l) ls) = length ls.
Proof. induction ls as [|b ls IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.

Definition pad_sh12 : list byte := repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 3 ++ repeat (Z_to_bv 8 (-13)) 5.

Lemma pad_segAI : forall (S f O BUF N FILL lo : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s9 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 h0 h1 h2 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 16%nat ->
  0 < f -> f + 128 <= lo -> 0xdc000 <= f / 8 -> f / 8 + 2147450880 + 16 <= lo -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0 < O -> O + 264 <= lo -> O mod 16 = 0 -> O / 8 + 2147450880 + 34 <= lo ->
  (O + 264 <= f \/ f + 128 <= O) -> (f + 128 <= O / 8 + 2147450880 \/ (O + 264) / 8 + 2147450880 <= f) ->
  (O + 264 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= O) ->
  0x7fff7f800000 <= lo -> lo <= S - 192 -> S < 2^63 -> 0 < BUF -> 0 <= N -> BUF + N < 2^63 -> 0 <= FILL < 256 ->
  bytes_at bsegs m (O / 8 + 2147450880) (repeat z8 33) ->
  rw_cells bsegs m (S - 192) (pad_locals0 j0 j1 j2 j3 j4 j5 j6 (BUF + N) j8 j9 j10) -> rw_cells bsegs m (O + 136) [C8 (wz 0)] ->
  rw_cells bsegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells bsegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xbe5c0) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz BUF) (wz (BUF + N)) (wz 0xbe53c) (wz (-13)) (wz (-8)) a5 a6 a7
                   (wz f) (wz (O + 8)) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xbe7b4) fc None m1 (seg_rom bsegs)
      /\ munch [(S - 192, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
     /\ rw_cells bsegs m1 (S - 192) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((O + 136) / 8 + 2147450880)); C8 (wz (O + 136)); C8 (wz BUF); C8 (wz ((O + 8) / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)]
      /\ rw_cells bsegs m1 (O + 136) [C8 (wz 0)]
      /\ rw_cells bsegs m1 f [C8 (wz 0x41b58ab3); C8 (wz 0x16b83); C8 (wz 0xbe53c)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 pad_sh12 ++ map (fun l => CB 1 l) (skipn 12 ls)))
    (MS (mkR (wz 0xbe5c0) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz f) a1 a2 a3 a4 a5 a6 a7
             s2 (wz (O + 8)) (wz 2147450880) (wz FILL) (wz (O + 112)) s7 (wz BUF) s9 (wz BUF) s11 t3 t4 t5 t6)
        F (wz 0xbe5c0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH OSH2 LOW LSP SPH B0 N0 BNH FIR SHZ0 FRl WID FH FS MI.
  do 16 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold pad_sh12, pad_locals0 in *. cbn [map app repeat skipn] in *.
  pose proof (munch_refl [(S - 192, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (S - 192)) = S - 192) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (O + 136)) = O + 136) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(S - 192, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m' -> wmono bsegs m m' -> shz m' O 264).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 33). apply (shz_of_zero_run m' O 33); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OSH OF FD8 F0 O0. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m (O / 8 + 2147450880) (repeat z8 33))) in SHZ0.
  do 3 zstep.
  zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  lstep.
  do 3 zstep. zstep. rewrite shr3_div. do 5 zstep.
  do 3 lstep.
  zstep. zstep.
  do 12 ls.
  zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  zstep.    replace (O + 112 + 24) with (O + 136) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (O + 136). zstep. shz_norm. zstep. if_false.
  lstep.
  zstep.
  zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  lstep.
  zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
  zstep.
  lstep.
  zstep.    replace (BUF - BUF) with 0 by lia.
  zstep.
  replace (Z.land (O + 8) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - O16; Z.div_mod_to_equations; lia).
  zstep. rewrite shr3_div. lstep.
  zstep. if_true.
  zstep. if_true.
  zstep. zstep.
  zstep.    replace (BUF + N - BUF) with N by lia.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma pad_segBI : forall (S f O BUF N lo : Z) (gp tp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j8 j9 : list byte) F fc (m : mem),
  0 < f -> f + 128 < 2^63 -> 0 < O -> O + 264 < 2^63 -> O mod 16 = 0 -> 0 <= S - 192 -> S < 2^63 -> 0 < BUF -> BUF + N < 2^63 -> 0 < N < 2^63 ->
  shz m O 264 -> shz m OSS_SBVT_A 8 ->
  rw_cells bsegs m (S - 192) [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz ((O + 136) / 8 + 2147450880)); C8 (wz (O + 136)); C8 (wz BUF); C8 (wz ((O + 8) / 8)); C8 (wz (BUF + N)); CB 8 j8; CB 8 j9; C8 (wz f)] ->
  rw_cells bsegs m (O + 8) [C8 (wz OSS_SB_VPTR_A)] ->
  ro_cells bsegs m OSS_SBVT_A [C8 (wz OSS_XSPUTN_A); C8 (wz OSS_OVERFLOW_A)] ->
  mem_inv bsegs m ->
  evt bsegs (eq (MS (mkR (wz 0xbe7f8) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz (O + 8)) (wz BUF) (wz N) (wz OSS_XSPUTN_A) (wz (-8)) a5 a6 a7
                        (wz f) (wz (O + 8)) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
                   F (wz OSS_XSPUTN_A) fc None m (seg_rom bsegs)))
    (MS (mkR (wz 0xbe5c0) (wz (S - 192)) gp tp t0 t1 t2 (wz S) (wz (S - 192)) (wz BUF) (wz (BUF + N)) (wz 0xbe53c) (wz (-13)) (wz (-8)) a5 a6 a7
             (wz f) (wz (O + 8)) (wz 2147450880) (wz N) (wz 0) (wz f) (wz BUF) (wz 0) (wz 0) (wz (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xbe7b4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH O0 OH O16 S0 SPH B0 BNH NR SHZ0 SHV FRl SB VT MI.
  unfold OSS_SBVT_A, OSS_XSPUTN_A, OSS_OVERFLOW_A, OSS_SB_VPTR_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 (S - 192)) = S - 192) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (O + 8)) = O + 8) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
  zstep. if_false.
  zstep. zstep.
  shz_pose SHZ0 (O + 8). zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep.
  pose proof (SHV 0x17d7a0 ltac:(lia)) as RD. change (0x17d7a0 / 8 + 2147450880) with 2147646196 in RD.
  zstep. shz_norm.
  zstep.
  zstep. if_false.
  zstep.
  do 3 zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
