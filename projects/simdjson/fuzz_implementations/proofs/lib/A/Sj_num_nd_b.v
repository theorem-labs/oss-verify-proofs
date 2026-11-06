(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_nd_defs Sj_num_nd_runs.
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
  Hypothesis FLO : (0x6d2000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6d2000 <= X /\ X + 504 <= lo)%Z.
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

  Definition nd_564_k : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 (mm : mem),
      nd_xinv X spq f m0 mm ->
      evt asegs Q (NDS 0xee19c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 mm).
  Hypothesis K564 : nd_564_k.

  Lemma nd_cmpl : forall (fuel : nat) (j xlen tlen : Z) xra xt0 xt1 xt2 xa2 xa3 xa5 xa6 xa7 xs3 xs5 xs9 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen tlen -> (-1 <= j < 62)%Z -> (j + 1 <= Z.of_nat fuel)%Z ->
    (forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys7 yt3 yt4 yt5 yt6,
       evt asegs Q (NDS 0xedff0 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs3 xs5 ys6 ys7 (Z_to_bv 64 (X + 496)) xs9 yt3 yt4 yt5 yt6 mm)) ->
    evt asegs Q (NDS 0xedfa0 xra xt0 xt1 xt2 (Z_to_bv 64 (X + 8 * j)) (Z_to_bv 64 (f + 32 + 8 * j)) xa2 xa3 (Z_to_bv 64 (j + 2)) xa5 xa6 xa7 xs3 xs5
                     (Z_to_bv 64 (X + 8 * j)) (Z_to_bv 64 (f + 32 + 8 * j)) (Z_to_bv 64 (X + 496)) xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH.
    intros fuel. induction fuel as [|fuel IH]; intros until mm; intros INV Hj Hf HK.
    all: pose proof INV as INV0; nd_open INV0; nd_env.
    all: astep.
    all: awalk ltac:(fun pc => lazymatch pc with
      | 0xedfa0%Z => first [ eapply evt_eq; [| eapply (IH (j - 1)%Z xlen tlen); [exact INV | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xedff0%Z => first [ eapply evt_eq; [| eapply HK]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_314 : forall (xlen tlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs9 xt3 xt4 xt5 xt6 c16 (mm : mem),
    NDINV (repeat (Z_to_bv 8 0) 63) c16 mm xlen tlen ->
    evt asegs Q (NDS 0xedf4c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (X + 496)) xs9 xt3 xt4 xt5 xt6 mm).
  Proof using NDH K564.
    intros until mm. intros INV. pose proof INV as INV0. nd_open INV0. nd_env.
    assert (DM3 : IsData xs3) by exact I. assert (DMc : IsData c24) by exact I.
    assert (K3B8 : forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 yt3 yt4 yt5 yt6,
              evt asegs Q (NDS 0xedff0 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs3 ys5 ys6 ys7 (Z_to_bv 64 (X + 496)) xs9 yt3 yt4 yt5 yt6 mm)).
    { intros. awalk ltac:(fun pc => lazymatch pc with 0xee0a0%Z => idtac end).
      all: num_cur_mem ltac:(fun m1 => eapply (nd_run2 f m1 ltac:(lia) Q); [exact TSH | exact MI | apply munch_refl | apply wmono_refl |];
        clear MI TSH; intros j' mm2 TSH MI MU' WM'; transport_after_call asegs m1 mm2 MU' WM'; clear MU' WM').
      all: unfold nd_564_k in K564; eapply K564; nd_xclose. }
    awalk ltac:(fun pc => lazymatch pc with
      | 0xedfa0%Z => first [ eapply evt_eq; [| eapply (nd_cmpl (Z.to_nat xlen) (xlen - 1)%Z xlen tlen); [exact INV | lia | lia | intros; eapply K3B8]]; num_st_eq | fail 100 "cut" pc ]
      | 0xedff0%Z => first [ eapply K3B8 | fail 100 "cut" pc ]
      end).
  Qed.
End NDB.
