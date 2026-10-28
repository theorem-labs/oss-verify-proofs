(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit Sj_num_nd_runs2 Sj_num_nd_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Ltac nnorm_ndc :=
  repeat match goal with
  | |- context [bv_swrap 32 (?p mod 4294967296 + ?k)] => rewrite (swrap32_zext_add p k) by lia
  | |- context [bv_swrap 32 (?p mod 4294967296)] => rewrite (swrap32_zext p) by lia
  end;
  nnorm_u.
Local Ltac nnorm ::= nnorm_ndc.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section NDA.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X p2 e lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 160 - d)%Z.
  Hypothesis ROOM : (lo + NDCB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6e0000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis PR : (- NDCB_RANGE <= p2 <= NDCB_RANGE)%Z.
  Hypothesis ER : (0 <= e <= NDCB_RANGE)%Z.
  Variable Q : machine_state -> Prop.
  Notation WA := [(spq, spq + 56); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.

  Notation NDS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 (Z_to_bv 64 S) (Z_to_bv 64 (p2 mod 4294967296)) xs5 (Z_to_bv 64 X) (Z_to_bv 64 (- e)) xs8 (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac nd_env :=
    destruct SPQ as [Hd Hspq]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof PR as PR'; pose proof ER as ER'; unfold NDCB_RANGE in PR', ER';
    pose proof F64 as F64'; pose proof FLO as FLO'; pose proof FSH as FSH'; pose proof FS0 as FS0';
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL; pose proof (f64_8 f F64) as F8.

  Definition nd_a_mset_k : Prop :=
    forall (t7 : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 w xt3 xt4 xt5 xt6 c0 c8 c16 c32 c40 (mm : mem),
      rw_cells bsegs mm spq (nd_spill f c0 c8 c16 c32 c40) ->
      rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] ->
      mem_inv bsegs mm -> munch WA m0 mm -> wmono bsegs m0 mm -> (-1076 <= t7 <= 3020)%Z ->
      evt bsegs Q (NDS 0x84bc4 (Z_to_bv 64 0xfb3f0) xt0 xt1 xt2 (Z_to_bv 64 (f + 40)) (Z_to_bv 64 0) (Z_to_bv 64 496) xa3 xa4 xa5 xa6 xa7 w (Z_to_bv 64 t7) (Z_to_bv 64 (f + 32))
                       (Z_to_bv 64 (0 - p2)) xt3 xt4 xt5 xt6 mm).

  Section KA.
  Hypothesis KMSET : nd_a_mset_k.

  Lemma nd_174 : forall (t7 : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 c0 c8 c16 c32 c40 jz (mm : mem),
    rw_cells bsegs mm spq (nd_spill f c0 c8 c16 c32 c40) ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    mem_inv bsegs mm -> munch WA m0 mm -> wmono bsegs m0 mm -> (-1076 <= t7 <= 3020)%Z ->
    evt bsegs Q (NDS 0xfb2dc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 t7) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (0 - p2)) xt3 xt4 xt5 xt6 mm).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0 PR ER KMSET.
    intros until mm. intros SPILL SHZ MI MU WM H7. unfold nd_spill in SPILL. nd_env.
    assert (DA0 : IsData xa0) by exact I. assert (DA1 : IsData xa1) by exact I.
    num_cur_mem ltac:(fun m1 => eapply (nd_run1 f m1 ltac:(lia) Q); [exact SHZ | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI SHZ; intros mm' SHZ MI MU' WM'; transport_after_call bsegs m1 mm' MU' WM'; clear MU' WM').
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfb770%Z => u_trap pc
      | 0x84bc4%Z => first [ eapply evt_eq; [| eapply (KMSET t7); [unfold nd_spill; exact SPILL | exact SHZ | exact MI | exact MU | exact WM | exact H7]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_a : forall xra xt0 xt1 xt2 xa6 xa7 xs2 xs5 xs8 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 jz (mm : mem),
    rw_cells bsegs mm spq [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48] ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    mem_inv bsegs mm -> munch WA m0 mm -> wmono bsegs m0 mm ->
    evt bsegs Q (NDS 0xfb214 xra xt0 xt1 xt2 (Z_to_bv 64 f) (Z_to_bv 64 (-13)) (Z_to_bv 64 p2) (Z_to_bv 64 107384) (Z_to_bv 64 1028088) (Z_to_bv 64 (-8)) xa6 xa7
                     xs2 xs5 xs8 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0 PR ER KMSET.
    intros until mm. intros SPILL SHZ MI MU WM. nd_env.
    assert (DS2 : IsData xs2) by exact I.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfb770%Z => u_trap pc
      | 0xfb2dc%Z => first [ eapply evt_eq; [| eapply nd_174 with (jz := jz)]; [num_st_eq | unfold nd_spill; eassumption | exact SHZ | exact MI | exact MU | exact WM | lia] | fail 100 "cut" pc ]
      end).
  Qed.
  End KA.
End NDA.
