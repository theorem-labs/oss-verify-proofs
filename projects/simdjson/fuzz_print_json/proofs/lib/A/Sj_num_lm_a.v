(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_lm_runs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMA.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 256 - d)%Z.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6c9000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6c9000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Variable Q : machine_state -> Prop.

  Notation WA := [(spq + 16, spq + 152); (f + 528, f + 530); (f / 8 + 2147450884, f / 8 + 2147450947)]%Z.

  Notation LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) xs4 xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition LMA_POST (mm : mem) (n : Z) (a16 a24 a32 a40 a48 a56 a64 a80 a88 a128 a136 : list byte) : Prop :=
    rw_cells asegs mm (spq + 16) [CB 8 a16; CB 8 a24; CB 8 a32; CB 8 a40; CB 8 a48; CB 8 a56; CB 8 a64; C8 (Z_to_bv 64 f); CB 8 a80; CB 8 a88;
                                  C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)); C8 (Z_to_bv 64 (X + 496)); C8 (Z_to_bv 64 X);
                                  CB 8 a128; CB 8 a136; C8 (Z_to_bv 64 f)] /\
    rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 n)] /\
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
    rw_cells asegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] /\
    rw_cells asegs mm (f + 528) [C2 (Z_to_bv 64 0)] /\
    mem_inv asegs mm /\ munch WA m0 mm /\ wmono asegs m0 mm.

  Definition lm_a_cpy_k : Prop :=
    forall (n : Z) xt0 xt1 xt2 xa4 xa5 xa7 xs6 xs7 xs8 xs11 xt3 xt6 a16 a24 a32 a40 a48 a56 a64 a80 a88 a128 a136 (mm : mem),
      LMA_POST mm n a16 a24 a32 a40 a48 a56 a64 a80 a88 a128 a136 -> (1 <= n <= 62)%Z ->
      evt asegs Q (LMS 0x8181c (Z_to_bv 64 0xe9774) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 X) (Z_to_bv 64 (8 * n)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880))
                       xa4 xa5 (Z_to_bv 64 (-8)) xa7 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 0x2e6c0) xs6 xs7 xs8 (Z_to_bv 64 5) xs11 xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) xt6 mm).

  Definition lm_a_d7c_k : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs11 xt3 xt6 a16 a24 a32 a40 a48 a56 a64 a80 a88 a128 a136 (mm : mem),
      LMA_POST mm 0 a16 a24 a32 a40 a48 a56 a64 a80 a88 a128 a136 ->
      evt asegs Q (LMS 0xe977c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 0x2e6c0) xs6 xs7 xs8 (Z_to_bv 64 5) xs11 xt3
                       (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) xt6 mm).

  Lemma lm_a : lm_a_cpy_k -> lm_a_d7c_k ->
    forall (n : Z) xra xt0 xt1 xt2 xa4 xa5 xa7 xs4 xs6 xs7 xs8 xs11 xt3 xt5 xt6 a16 a24 a32 a40 a48 a56 a64 a80 a88 a96 a104 a112 a128 a136 a144 jz jzl (mm : mem),
    rw_cells asegs mm (spq + 16) [CB 8 a16; CB 8 a24; CB 8 a32; CB 8 a40; CB 8 a48; CB 8 a56; CB 8 a64; C8 (Z_to_bv 64 f); CB 8 a80; CB 8 a88; CB 8 a96; CB 8 a104; CB 8 a112;
                                  C8 (Z_to_bv 64 X); CB 8 a128; CB 8 a136; CB 8 a144] ->
    rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 n)] -> (0 <= n <= 62)%Z ->
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jz] ->
    rw_cells asegs mm (f + 528) [CB 2 jzl] ->
    mem_inv asegs mm -> munch WA m0 mm -> wmono asegs m0 mm ->
    evt asegs Q (LMS 0xe9634 xra xt0 xt1 xt2 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (-13)) (Z_to_bv 64 ((X + 496) / 8)) (Z_to_bv 64 (-14))
                     xa4 xa5 (Z_to_bv 64 (-8)) xa7 (Z_to_bv 64 f) xs4 (Z_to_bv 64 0x2e6c0) xs6 xs7 xs8 (Z_to_bv 64 5) xs11 xt3 (Z_to_bv 64 X) xt5 xt6 mm).
  Proof using SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP.
    intros KCPY KD7C. intros until mm. intros SPILL XN LEN ZR SHZ ZLEN MI MU WM.
    destruct SPQ as [Hd Hspq]. unfold LMA_STACK, RT_STACK, USTACK_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    awalk ltac:(fun pc => lazymatch pc with 0xe9654%Z => idtac end).
    num_cur_mem ltac:(fun m1 => eapply (lm_run1 f m1 ltac:(lia) Q); [exact SHZ | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI; intros mm' SHZ' MI' MU' WM'; transport_after_call asegs m1 mm' MU' WM'; clear MU' WM').
    awalk ltac:(fun pc => lazymatch pc with
      | 0x8181c%Z => first [ eapply evt_eq; [| eapply (KCPY n); [repeat (split; [eassumption|]); eassumption | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe977c%Z => first [ subst n; eapply evt_eq; [| eapply KD7C; repeat (split; [eassumption|]); eassumption]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End LMA.
