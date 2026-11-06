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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_nd_defs Sj_num_nd_runs Sj_num_nd_b Sj_num_nd_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section NDB.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 160 - d)%Z.
  Hypothesis ROOM : (lo + NDCA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6c2000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6c2000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= S \/ S + 128 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 128 <= X / 8 + 2147450880))%Z.
  Variable Q : machine_state -> Prop.
  Collection NDH := SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP.
  Notation NDINV := (nd_inv X spq f m0).

  Notation NDS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac nd_env :=
    destruct SPQ as [Hd Hspq]; unfold NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let F8 := fresh "F8" in pose proof (f64_8 f F64) as F8;
    let F32 := fresh "F32" in assert (F32 : ((f + 32) / 8 = f / 8 + 4)%Z) by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; apply f64_div; exact F64).

  Notation b_314 := (nd_314 sp gp tp F fc X lo d spq f m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP Q).
  Hypothesis K564 : nd_564_k sp gp tp F fc X spq f m0 Q.
  Variable e : Z.
  Hypothesis KP5 : nd_p5_k sp gp tp F fc X spq f m0 Q e.
  Hypothesis KMVT : nd_mvt_k sp gp tp F fc X spq f m0 Q.
  Hypothesis KMST : nd_mst_k sp gp tp F fc X spq f m0 Q.
  Hypothesis KMVX : nd_mvx_k sp gp tp F fc X spq f m0 Q.
  Hypothesis KMSX : nd_msx_k sp gp tp F fc X spq f m0 Q.
  Notation c_0f0 := (nd_0f0 sp gp tp F fc X lo d spq f m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP Q K564 KMVT KMVX).
  Ltac nd_cut_314 := first [ eapply evt_eq; [| eapply (b_314 K564); nd_close]; num_st_eq ].

  Lemma nd_1cc : forall (k n xlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen n -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
    evt asegs Q (NDS 0xe13e8 (Z_to_bv 64 0xe13e8) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 X) (Z_to_bv 64 (8 * k))
                     (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using NDH KMST.
    intros until mm. intros INV Hk Hn Hkn. pose proof INV as INV0. nd_open INV0. nd_env.
    awalk ltac:(fun pc => lazymatch pc with
      | 0x7f574%Z => first [ unfold nd_mst_k in KMST; eapply evt_eq; [| eapply (KMST k n xlen); [exact INV | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_1e0 : forall (k n xlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen n -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
    evt asegs Q (NDS 0xe13fc (Z_to_bv 64 0xe13fc) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 (Z_to_bv 64 X)
                     (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using NDH K564.
    intros until mm. intros INV Hk Hn Hkn. nd_open INV. nd_env.
    assert (DM3 : IsData xs3) by exact I.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe1530%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_2f0 : forall (k n tlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 (8 * k)) mm n tlen -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
    evt asegs Q (NDS 0xe150c (Z_to_bv 64 0xe150c) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 X)
                     (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using NDH KMSX.
    intros until mm. intros INV Hk Hn Hkn. pose proof INV as INV0. nd_open INV0. nd_env.
    awalk ltac:(fun pc => lazymatch pc with
      | 0x7f574%Z => first [ unfold nd_msx_k in KMSX; eapply evt_eq; [| eapply (KMSX k n tlen); [exact INV | lia | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_300 : forall (k n tlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm n tlen -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
    evt asegs Q (NDS 0xe151c (Z_to_bv 64 0xe151c) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 X)
                     (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using NDH K564.
    intros until mm. intros INV Hk Hn Hkn. nd_open INV. nd_env.
    assert (DM3 : IsData xs3) by exact I.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe1530%Z => first [ nd_cut_314 | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_0d0 : forall (xlen : Z) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs9 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 xbs tbs jt (mm : mem),
    rw_cells asegs mm spq [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48] ->
    u8arr asegs mm X xbs -> length xbs = 496%nat -> rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] -> (0 <= xlen <= 62)%Z ->
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    u8arr asegs mm (f + 32) tbs -> length tbs = 496%nat -> rw_cells asegs mm (f + 528) [CB 2 jt] ->
    rw_cells asegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] ->
    mem_inv asegs mm -> munch (nd_W X spq f) m0 mm -> wmono asegs m0 mm -> (0 <= e < 2147483648)%Z ->
    evt asegs Q (NDS 0xe12ec (Z_to_bv 64 0xe12ec) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 X) xs6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (- e)) xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH K564 KMVX KMVT KP5.
    intros until mm. intros SPILL XA XL XN LEN ZR TA TL TN TSH MI MU WM He. nd_env. unfold nd_W in MU.
    assert (DM3 : IsData xs3) by exact I. assert (DM6 : IsData xs6) by exact I. assert (DM9 : IsData xs9) by exact I.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe130c%Z => first [ eapply evt_eq; [| eapply (c_0f0 xlen 1%Z); nd_close]; num_st_eq | fail 100 "cut" pc ]
      | 0xe1884%Z => first [ unfold nd_p5_k in KP5; eapply evt_eq; [| eapply (KP5 xlen); nd_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End NDB.
