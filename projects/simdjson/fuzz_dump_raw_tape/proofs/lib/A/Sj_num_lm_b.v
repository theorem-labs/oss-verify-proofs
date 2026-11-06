(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMB.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f Y : Z) (ybs : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 256 - d)%Z.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6c2000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6c2000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Hypothesis YR : (0 <= Y /\ Y + 40 <= 0x6c2000 /\ Y mod 8 = 0)%Z.
  Hypothesis YL : length ybs = 40%nat.
  Hypothesis SHPY : forall m', munch (lm_WL X spq f) m0 m' -> wmono asegs m0 m' -> shz m' Y 40.
  Notation LMINV := (lm_inv X spq f Y ybs m0).
  Variable Q : machine_state -> Prop.

  Notation LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) xs4 xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Notation lm_head_k := (lm_head_k sp gp tp F fc X spq f Y ybs m0 Q 1).
  Notation lm_exit_k := (lm_exit_k sp gp tp F fc X spq f m0 Q).

  Lemma lm_b : lm_head_k -> lm_exit_k ->
    forall (n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs11 xt3 xt6 a16 a24 a32 a40 a48 a56 a64 a80 a88 a128 a136 xbs zibs jzl jzi (mm : mem),
    rw_cells asegs mm (spq + 16) [CB 8 a16; CB 8 a24; CB 8 a32; CB 8 a40; CB 8 a48; CB 8 a56; CB 8 a64; C8 (Z_to_bv 64 f); CB 8 a80; CB 8 a88;
                                  C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)); C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 X);
                                  CB 8 a128; CB 8 a136; C8 (Z_to_bv 64 f)] ->
    u8arr asegs mm X xbs -> length xbs = 496%nat ->
    rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 n)] -> (0 <= n <= 62)%Z ->
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells asegs mm (f + 528) [C2 (Z_to_bv 64 0)] ->
    u8arr asegs mm (f + 608) zibs -> length zibs = 496%nat ->
    rw_cells asegs mm (f + 1104) [CB 2 jzl] ->
    rw_cells asegs mm (f / 8 + 2147450956) [CB 63 jzi] ->
    bytes_at asegs mm Y ybs ->
    mem_inv asegs mm -> munch (lm_WL X spq f) m0 mm -> wmono asegs m0 mm ->
    evt asegs Q (LMS 0xe1f98 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 Y) xs6 xs7 xs8 (Z_to_bv 64 5) xs11 xt3
                     (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) xt6 mm).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YR YL SHPY.
    intros KHEAD KEXIT. unfold Sj_num_lm_defs.lm_head_k in KHEAD. unfold Sj_num_lm_defs.lm_exit_k in KEXIT. intros until mm. intros SPILL XA XL XN LEN ZR ZLEN ZIA ZIL ZIC ZSH YB MI MU WM.
    destruct SPQ as [Hd Hspq]. unfold LMA_STACK, RT_STACK, USTACK_TOP in *. unfold lm_WL in MU.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    assert (F608 : ((f + 608) / 8 = f / 8 + 76)%Z) by (replace (f + 608)%Z with (f + 8 * 76)%Z by lia; apply f64_div; exact F64).
    assert (KREST : forall (xlen' : Z) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xbs' (mm' : mem),
              rw_cells asegs mm' (spq + 16) [CB 8 a16; CB 8 a24; CB 8 a32; CB 8 a40; CB 8 a48; CB 8 a56; CB 8 a64; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 n);
                                  C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)); C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 X);
                                  CB 8 a128; CB 8 a136; C8 (Z_to_bv 64 f)] ->
              u8arr asegs mm' X xbs' -> length xbs' = 496%nat -> rw_cells asegs mm' (X + 496) [C2 (Z_to_bv 64 xlen')] -> (0 <= xlen' <= 62)%Z ->
              bytes_at asegs mm' (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
              u8arr asegs mm' (f + 608) zibs -> rw_cells asegs mm' (f + 1104) [CB 2 jzl] -> rw_cells asegs mm' (f / 8 + 2147450956) [CB 63 jzi] ->
              bytes_at asegs mm' Y ybs -> mem_inv asegs mm' -> munch (lm_WL X spq f) m0 mm' -> wmono asegs m0 mm' ->
              evt asegs Q (LMS 0xe205c yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 f) (Z_to_bv 64 xlen') (Z_to_bv 64 Y) xs6 xs7 xs8 (Z_to_bv 64 5) xs11 xt3
                               (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) xt6 mm')).
    { clear SPILL XA XL XN ZR ZLEN ZIA ZIC ZSH YB MI MU WM. intros until mm'. intros SPILL XA XL XN LEN' ZR ZIA ZIC ZSH YB MI MU WM. unfold lm_WL in MU.
      awalk ltac:(fun pc => lazymatch pc with
        | 0xe227c%Z => first [ rewrite F608 in SPILL; replace (2147450880 + (f / 8 + 76))%Z with (f / 8 + 2147450956)%Z in SPILL by lia;
                               apply cb2_c2 in ZIC; eapply evt_eq; [| eapply (KHEAD 1%Z); [lm_close | lia]]; num_st_eq | fail 100 "cut" pc ]
        end). }
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe1fe4%Z => idtac
      | 0xe205c%Z => first [ rewrite ?Z.add_0_l in *; eapply evt_eq; [| eapply (KREST n); try eassumption; lia]; num_st_eq | fail 100 "cut" pc ]
      end).
    rewrite ?Z.add_0_l in *.
    num_cur_mem ltac:(fun m1 =>
      eapply evt_eq; [| eapply (lm_mulx X lo m1 X8 ltac:(lia) XSH XS0 Q (Z.to_nat n) 0%Z n); [exact XA | exact XL | exact ZR | exact MI | apply munch_refl | apply wmono_refl | lia | lia | lia |]]; [num_st_eq|];
      clear MI; intros a0' a1' a3' a4' a6' a7' xbs' mm' XA' XL' MI' MU' WM'; clear XA; transport_after_call asegs m1 mm' MU' WM'; clear MU' WM').
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe205c%Z => first [ eapply evt_eq; [| eapply KREST; try eassumption; lia]; num_st_eq | fail 100 "cut" pc ]
      | 0xe299c%Z => first [ eapply KEXIT; lm_xclose | fail 100 "cut" pc ]
      end).
  Qed.
End LMB.
