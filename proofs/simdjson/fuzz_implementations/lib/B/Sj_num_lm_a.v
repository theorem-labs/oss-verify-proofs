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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit Sj_num_lm_runs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section LMA.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 224 - d)%Z.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6e0000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6e0000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Variable Q : machine_state -> Prop.

  Notation WA := [(spq, spq + 120); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.

  Notation LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) (Z_to_bv 64 X) xs5 xs6
             (Z_to_bv 64 2147450880) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition LMA_POST (mm : mem) (n : Z) (a0 a8 a16 a24 a56 a72 a96 a104 : list byte) : Prop :=
    rw_cells bsegs mm spq [CB 8 a0; CB 8 a8; CB 8 a16; CB 8 a24; C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)); C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f);
                           CB 8 a56; C8 (Z_to_bv 64 f); CB 8 a72; C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 5); CB 8 a96; CB 8 a104; C8 (Z_to_bv 64 f)] /\
    rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 n)] /\
    bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] /\
    rw_cells bsegs mm (f + 528) [C2 (Z_to_bv 64 0)] /\
    mem_inv bsegs mm /\ munch WA m0 mm /\ wmono bsegs m0 mm.

  Definition lm_a_cpy_k (n : Z) : Prop :=
    forall xt0 xt2 xa7 xs6 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a56 a72 a96 a104 (mm : mem),
      LMA_POST mm n a0 a8 a16 a24 a56 a72 a96 a104 -> (1 <= n <= 62)%Z ->
      evt bsegs Q (LMS 0x84728 (Z_to_bv 64 0xfc25c) xt0 (Z_to_bv 64 5) xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 X) (Z_to_bv 64 (8 * n)) (Z_to_bv 64 (-14))
                       (Z_to_bv 64 93077) (Z_to_bv 64 1031612) (Z_to_bv 64 f) xa7 (Z_to_bv 64 n) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs6
                       (Z_to_bv 64 (18446744073709551615 - (f + 32))) (Z_to_bv 64 (8 * n)) (Z_to_bv 64 B_P5LARGE) xs11 xt3 xt4 xt5 xt6 mm).

  Definition lm_a_100_k (n : Z) : Prop :=
    forall xra xt0 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a56 a72 a96 a104 (mm : mem),
      LMA_POST mm n a0 a8 a16 a24 a56 a72 a96 a104 -> n = 0%Z ->
      evt bsegs Q (LMS 0xfc268 xra xt0 (Z_to_bv 64 5) xt2 (Z_to_bv 64 (f + 32)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 n) xs5 xs6 xs8 xs9 (Z_to_bv 64 B_P5LARGE) xs11
                       xt3 xt4 xt5 xt6 mm).

  Lemma lm_a : forall (n : Z), lm_a_cpy_k n -> lm_a_100_k n ->
    forall xt0 xt2 xa7 xs2 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a32 a56 a64 a72 a80 a96 a104 a112 jz jzl (mm : mem),
    rw_cells bsegs mm spq [CB 8 a0; CB 8 a8; CB 8 a16; CB 8 a24; CB 8 a32; C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 f); CB 8 a56; CB 8 a64; CB 8 a72; CB 8 a80;
                           C8 (Z_to_bv 64 5); CB 8 a96; CB 8 a104; CB 8 a112] ->
    rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 n)] -> (0 <= n <= 62)%Z ->
    bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    rw_cells bsegs mm (f + 528) [CB 2 jzl] ->
    mem_inv bsegs mm -> munch WA m0 mm -> wmono bsegs m0 mm ->
    evt bsegs Q (LMS 0xfc10c (Z_to_bv 64 0xfbe38) xt0 (Z_to_bv 64 5) xt2 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-14))
                     (Z_to_bv 64 93077) (Z_to_bv 64 1031612) (Z_to_bv 64 f) xa7 xs2 (Z_to_bv 64 ((X + 496) / 8)) xs6 (Z_to_bv 64 B_P5LARGE) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP.
    intros n KCPY K100. intros until mm. intros SPILL XN LEN ZR SHZ ZLEN MI MU WM.
    destruct SPQ as [Hd Hspq]. unfold LMB_STACK, RT_STACK, USTACK_TOP, B_P5LARGE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    bwalk ltac:(fun pc => lazymatch pc with 0xfc12c%Z => idtac | 0xfcc40%Z => u_trap pc end).
    num_cur_mem ltac:(fun m1 => eapply (lm_run1 f m1 ltac:(lia) Q); [exact SHZ | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI SHZ; intros mm' SHZ' MI' MU' WM'; transport_after_call bsegs m1 mm' MU' WM'; clear MU' WM').
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcc40%Z => u_trap pc
      | 0x84728%Z => first [ eapply evt_eq; [| eapply KCPY; [repeat (split; [eassumption|]); eassumption | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xfc268%Z => first [ eapply evt_eq; [| eapply K100; [repeat (split; [eassumption|]); eassumption | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End LMA.
