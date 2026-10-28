(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_bcall Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_n Sj_num_lm_c3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section LMB.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f len0 : Z) (ybs : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := B_P5LARGE.
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 224 - d)%Z.
  Hypothesis ROOM : (lo + LMB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6cd000 <= f /\ f + 2040 <= lo)%Z.
  Hypothesis FSH : (f + 2040 <= S \/ S + 255 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XR : (0x6cd000 <= X /\ X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
       /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
       /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.
  Hypothesis YL : length ybs = 40%nat.
  Hypothesis SHPY : forall m', munch (lm_WL X spq f) m0 m' -> wmono bsegs m0 m' -> shz m' Y 40.
  Hypothesis BCP : forall m', munch (lm_WL X spq f) m0 m' -> wmono bsegs m0 m' -> b_consts m'.
  Hypothesis L0 : (0 <= len0 <= 62)%Z.
  Variable Q : machine_state -> Prop.
  Collection LMH := SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YL SHPY BCP L0.
  Notation CAPL := (len0 + 6 <= 62)%Z.
  Notation zl := len0.
  Notation LMINV := (lm_inv X spq f lo ybs m0).
  Notation LMARGS := (sp gp tp F fc X lo d spq f len0 ybs m0) (only parsing).

  Notation LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) (Z_to_bv 64 X) xs5 xs6
             (Z_to_bv 64 2147450880) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation LJ pc j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs11 xt3 xt4 xt5 xt6 mm :=
    (LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (-8)) (Z_to_bv 64 (8 * zl)) (Z_to_bv 64 18446744073709375359) xs8 (Z_to_bv 64 (f + 608)) (Z_to_bv 64 j) xs11
         xt3 xt4 xt5 xt6 mm).

  Ltac lm_env :=
    destruct SPQ as [Hd Hspq]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof F64 as F64'; pose proof FLO as FLO'; pose proof FSH as FSH'; pose proof FS0 as FS0'; pose proof X8 as X8'; pose proof XR as XR';
    pose proof XSH as XSH'; pose proof XS0 as XS0'; pose proof SEP as SEP'; pose proof YL as YL'; pose proof L0 as L0'; unfold B_P5LARGE in *;
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL; pose proof (f64_8 f F64) as F8.

  Hypothesis KEXIT : lm_exit_k sp gp tp F fc X lo spq f len0 m0 Q.
  Hypothesis KCPY2 : lm_cpy2_k sp gp tp F fc X lo spq f len0 ybs m0 Q 1.
  Notation lm_f960 := (lm_f960 sp gp tp F fc X lo d spq f len0 ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YL SHPY BCP L0 Q KEXIT).
  Notation lm_J := (lm_J sp gp tp F fc X lo d spq f len0 ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YL SHPY BCP L0 Q KEXIT 1%Z KCPY2).

  Lemma lm_1f0 : forall xra xt0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a56 a72 a96 a104 zsh ziw (mm : mem) len,
    LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw mm len False -> (CAPL -> len <= zl + 1)%Z ->
    evt bsegs Q (LMS 0xed270 xra xt0 (Z_to_bv 64 5) (Z_to_bv 64 zl) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 (Z_to_bv 64 Y) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT KCPY2.
    intros until len. intros INV HB. pose proof INV as INV0. lm_open INV0. lm_env.
    assert (S48 : (Z.shiftl zl 48 mod 18446744073709551616 = zl * 281474976710656)%Z) by (apply shl48_small; lia).
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xedb58%Z => u_trap pc
      | 0xed480%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillL X f zl a0 a96 a104) zsh ziw m1 len False) by lm_close);
                             eapply evt_eq; [| eapply (lm_J 4%nat 1%Z)]; [num_st_eq | lia | lia | lia | exact INV1 | intros HC; pose proof (HB HC); lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_S1 : forall (fu : nat) (i N : Z) xra xt0 xa1 xa2 xa7 xs5 xs6 xs9 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a56 a72 a96 a104 zsh ziw (mm : mem),
    LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw mm len0 False -> (0 <= i < len0)%Z -> (62 <= N < 2305843009213693952)%Z -> (len0 - i <= Z.of_nat fu)%Z ->
    evt bsegs Q (LMS 0xed1dc xra xt0 (Z_to_bv 64 5) (Z_to_bv 64 zl) (Z_to_bv 64 (X + 8 * i)) xa1 xa2 (Z_to_bv 64 (N - i)) (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (X + 8 * i))
                     (Z_to_bv 64 (len0 - i)) xa7 (Z_to_bv 64 len0) xs5 xs6 (Z_to_bv 64 Y) xs9 (Z_to_bv 64 Y) xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT KCPY2.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV Hi HN Hf; [exfalso; lia|].
    pose proof INV as INV0. lm_open INV0. lm_env.
    assert (DA1 : IsData xa1) by exact I. assert (DA2 : IsData xa2) by exact I.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xedb58%Z => u_trap pc
      | 0xed9e0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw m1 len0 False) by lm_close);
                             eapply lm_f960; [exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      | 0xed270%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw m1 len0 False) by lm_close);
                             eapply evt_eq; [| eapply lm_1f0]; [num_st_eq | exact INV1 | intros HC; lia]
                           | num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw m1 (len0 + 1) False) by lm_close);
                             eapply evt_eq; [| eapply lm_1f0]; [num_st_eq | exact INV1 | intros HC; lia]
                           | fail 100 "cut" pc ]
      | 0xed1dc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw m1 len0 False) by lm_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z N)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_b : forall xra xt0 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a56 a72 a96 a104 zsh ziw (mm : mem),
    LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw mm len0 False ->
    rw_cells bsegs mm (f + 528) [C2 (Z_to_bv 64 0)] ->
    evt bsegs Q (LMS 0xed180 xra xt0 (Z_to_bv 64 5) xt2 (Z_to_bv 64 (f + 32)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 len0) xs5 xs6 xs8 xs9 (Z_to_bv 64 Y) xs11
                     xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT KCPY2.
    intros until mm. intros INV ZLEN. pose proof INV as INV0. lm_open INV0. lm_env.
    pose proof (bytes_at_bound _ _ _ _ YB) as YBD.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xedb58%Z => u_trap pc
      | 0xed270%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw m1 len0 False) by lm_close);
                             eapply evt_eq; [| eapply lm_1f0]; [num_st_eq | exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      | 0xed1dc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw m1 len0 False) by lm_close);
                             eapply evt_eq; [| eapply (lm_S1 (Z.to_nat len0) 0%Z ((0 - X) mod 18446744073709551616 / 8)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_0f4 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a56 a72 a96 a104 zsh ziw (mm : mem),
    LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw mm len0 False ->
    rw_cells bsegs mm (f + 528) [C2 (Z_to_bv 64 0)] ->
    evt bsegs Q (LMS 0xed174 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 len0) xs5 xs6 (Z_to_bv 64 (18446744073709551615 - (f + 32))) (Z_to_bv 64 (8 * len0))
                     (Z_to_bv 64 Y) xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT KCPY2.
    intros until mm. intros INV ZLEN. pose proof INV as INV0. lm_open INV0. lm_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xedb58%Z => u_trap pc
      | 0xed180%Z => first [ eapply evt_eq; [| eapply lm_b]; [num_st_eq | exact INV | exact ZLEN] | fail 100 "cut" pc ]
      end).
  Qed.
End LMB.
