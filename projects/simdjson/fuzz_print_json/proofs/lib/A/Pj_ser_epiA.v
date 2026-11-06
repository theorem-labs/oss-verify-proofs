(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_proA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma ser_epi1 : forall (q b f SB DOC : Z) (gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xra : word)
    (w168 w224 w232 w240 h0 h1 h2 : word) (x : xjA) F fc (m : mem),
  0 < f -> f + 512 <= b -> f / 8 + 2147450880 + 64 <= b -> 8 * (f / 8) = f ->
  (f + 512 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 64 <= f) -> b + 384 <= q -> q + 16 <= USTACK_TOP ->
  rw_cells asegs m b (ser_frame_raw f SB DOC w168 w224 w232 w240 x) -> rw_cells asegs m f [C8 h0; C8 h1; C8 h2] ->
  stk asegs m (f / 8 + 2147450880) (f / 8 + 2147450944) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a2' : word),
      ms = MS (mkR (wz 0xb546c) (wz b) gp (wz TPV_A) xt0 xt1 xt2 (wz q) (wz b) (wz (f / 8 + 2147450880)) (wz 64) a2' xa3 xa4 xa5 xa6 xa7
                   (wz f) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (wz (e_set_shadow 245)) fc None m1 (seg_rom asegs)
      /\ munch [(f, f + 8); (f / 8 + 2147450934, f / 8 + 2147450936)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 b (ser_frame_raw f SB DOC w168 w224 w232 w240 x) /\ rw_cells asegs m1 f [C8 (wz 0x45e0360e); C8 h1; C8 h2]
      /\ stk asegs m1 (f / 8 + 2147450880) (f / 8 + 2147450944))
    (MS (mkR xra (wz b) gp (wz TPV_A) xt0 xt1 xt2 (wz q) (wz b) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (wz PJ_EXIT_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FLO SFL Ef SHf BQ QT FR FH SHS MI.
  unfold PJ_EXIT_A, e_set_shadow, TPV_A, USTACK_TOP, ser_frame_raw in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450934, f / 8 + 2147450936)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).

  zstep. step. step. rewrite (le1_lit (-8)). pj_store_done. step. rewrite (le1_lit (-8)). pj_store_done.

  zstep. zstep. step. ls. step. step. if_cases K0; zify_cond K0; [exfalso; pjnorm_in K0; lia| clear K0]. zstep. zstep.
  apply evt_done. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros y Hy; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption| eassumption].
Qed.

Lemma ser_epi2 : forall (q b f fl lo : Z) (gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xra : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FRC : list cell) F fc (m : mem),
  0 < f -> f + 512 <= lo -> 0 < fl -> fl + 1 <= lo -> 0x6c9000 <= lo -> lo <= b -> cells_size FRC = 280%nat -> b + 384 <= q -> q + 16 <= USTACK_TOP -> b + 280 <= q - 104 ->
  stk asegs m lo b -> rw_cells asegs m b FRC -> stk asegs m (b + 280) (q - 104) ->
  rw_cells asegs m (q - 104) (sa_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ro_cells asegs m (f + 504) [C8 (wz fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem), ret_st ra (wz q) gp (wz TPV_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz fl) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR (wz 0xb546c) (wz b) gp (wz TPV_A) xt0 xt1 xt2 (wz q) (wz b) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (wz f) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (wz 0xb546c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LOB SZ BQ QT GB ST FR GAP FS FW FLC MI.
  unfold TPV_A, USTACK_TOP, sa_savedA in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

  zstep. ls. step. zstep.
  replace (q - 104) with (q + -104) in FS by lia.

  do 13 zstep. zstep.
  replace (q + -104) with (q - 104) in FS by lia.
  pose proof (stk_release asegs _ _ _ _ ST FR ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 280%nat) with 280 in ST1.
  pose proof (stk_merge asegs _ _ _ _ ST1 GAP ltac:(lia)) as ST2.
  pose proof (stk_release asegs _ _ _ _ ST2 FS ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (q - 104 + Z.of_nat 104) with q in ST3 by lia. replace (q + -384 + 384) with q by lia.

  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
