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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit Sj_num_lm_runs3 Sj_num_lm_defs.
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

Section LMN.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo d spq f len0 : Z) (ybs : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := B_P5LARGE.
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
    (LMS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (-8)) (Z_to_bv 64 (8 * zl)) (Z_to_bv 64 18446744073709356575) xs8 (Z_to_bv 64 (f + 608)) (Z_to_bv 64 j) xs11
         xt3 xt4 xt5 xt6 mm).

  Ltac lm_env :=
    destruct SPQ as [Hd Hspq]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof F64 as F64'; pose proof FLO as FLO'; pose proof FSH as FSH'; pose proof FS0 as FS0'; pose proof X8 as X8'; pose proof XR as XR';
    pose proof XSH as XSH'; pose proof XS0 as XS0'; pose proof SEP as SEP'; pose proof YL as YL'; pose proof L0 as L0'; unfold B_P5LARGE in *;
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL; pose proof (f64_8 f F64) as F8.

  Hypothesis KEXIT : lm_exit_k sp gp tp F fc X lo spq f len0 m0 Q.

  Lemma lm_f960 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 a0 a8 a16 a24 a56 a72 a96 a104 zsh ziw (mm : mem) len,
    LMINV (lm_spillB X f a0 a8 a16 a24 a56 a72 a96 a104) zsh ziw mm len False -> (CAPL -> False) ->
    evt bsegs Q (LMS 0xfcac8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT.
    intros until len. intros INV HF. pose proof INV as INV0. lm_open INV0. lm_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcad0%Z => first [ assert (XI : lm_xinv X spq f lo m0 mm len False) by (lm_xclose_with ltac:(let HH := fresh in intros HH; exact (False_ind _ HH)));
                             eapply evt_eq; [| eapply (KEXIT 0%Z len False); [exact XI | intros HC; exfalso; exact (HF HC)]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_f858 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 a0 a96 a104 zsh ziw (mm : mem) len,
    LMINV (lm_spillL X f zl a0 a96 a104) zsh ziw mm len False -> (CAPL -> False) ->
    evt bsegs Q (LMS 0xfc9c0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT.
    intros until len. intros INV HF. pose proof INV as INV0. lm_open INV0. lm_env.
    bwalk ltac:(fun pc => lazymatch pc with 0xfc9c8%Z => idtac end).
    num_cur_mem ltac:(fun m1 => eapply (lm_run4 f m1 ltac:(lia) Q); [exact ZSH | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI ZSH; intros zsh' mm' ZSH MI MU' WM'; transport_after_call bsegs m1 mm' MU' WM'; clear MU' WM').
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcad0%Z => first [ num_cur_mem ltac:(fun m1 => assert (XI : lm_xinv X spq f lo m0 m1 len False) by (lm_xclose_with ltac:(let HH := fresh in intros HH; exact (False_ind _ HH))));
                             eapply evt_eq; [| eapply (KEXIT 0%Z len False); [exact XI | intros HC; exfalso; exact (HF HC)]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_N : forall (fu : nat) (k : Z) xra xt0 xt1 xt2 xa0 xa4 xs2 xs5 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 a0 a96 a104 zsh ziw (mm : mem),
    LMINV (lm_spillL X f zl a0 a96 a104) zsh ziw mm k False -> (1 <= k)%Z -> (k <= Z.of_nat fu)%Z -> (CAPL -> k <= len0 + 6)%Z ->
    evt bsegs Q (LMS 0xfc398 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 k) (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 ((X + 496) mod 8 + 1)) xa4 (Z_to_bv 64 f)
                     (Z_to_bv 64 (X + 496)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) xs2 xs5 xs6 (Z_to_bv 64 1) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT.
    intros fu. induction fu as [|fu IH]; intros until mm; intros INV Hk Hf HB; [exfalso; lia|].
    pose proof INV as INV0. lm_open INV0. lm_env.
    bkstep.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xfcc40%Z => u_trap pc
      | 0xfcad0%Z => first [ fold_limbz; lazymatch goal with
                             | KBL : (bv_unsigned (limbz _ _) <> 0)%Z |- _ =>
                                 assert (XI : lm_xinv X spq f lo m0 mm k True) by (lm_xclose_with ltac:(intros _; right; lazymatch type of KBL with (bv_unsigned (limbz _ ?o) <> _)%Z => replace (8 * (k - 1))%Z with o by lia; exact KBL end));
                                 eapply evt_eq; [| eapply (KEXIT 1%Z k True); [exact XI | intros HC; split; [exact I | split; [reflexivity | lia]]]]; num_st_eq
                             | _ =>
                                 num_cur_mem ltac:(fun m1 => assert (XI : lm_xinv X spq f lo m0 m1 (k + -1) True) by (lm_xclose_with ltac:(intros _; left; lia)));
                                 eapply evt_eq; [| eapply (KEXIT 1%Z (k + -1)%Z True); [exact XI | intros HC; split; [exact I | split; [reflexivity | lia]]]]; num_st_eq
                             end | fail 100 "cut" pc ]
      | 0xfc398%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV (lm_spillL X f zl a0 a96 a104) zsh ziw m1 (k + -1) False) by lm_close);
                             eapply evt_eq; [| eapply (IH (k + -1)%Z)]; [num_st_eq | exact INV1 | lia | lia | intros HC; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_norm : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 a0 a96 a104 zsh ziw (mm : mem) len,
    LMINV (lm_spillL X f zl a0 a96 a104) zsh ziw mm len False -> (CAPL -> len <= len0 + 6)%Z ->
    evt bsegs Q (LMS 0xfc364 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT.
    intros until len. intros INV HB. pose proof INV as INV0. lm_open INV0. lm_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcc40%Z => u_trap pc
      | 0xfcad0%Z => first [ assert (XI : lm_xinv X spq f lo m0 mm len True) by (lm_xclose_with ltac:(intros _; left; lia));
                             eapply evt_eq; [| eapply (KEXIT 1%Z len True); [exact XI | intros HC; split; [exact I | split; [reflexivity | lia]]]]; num_st_eq | fail 100 "cut" pc ]
      | 0xfc398%Z => first [ eapply evt_eq; [| eapply (lm_N (Z.to_nat len) len)]; [num_st_eq | exact INV | lia | lia | exact HB] | fail 100 "cut" pc ]
      end).
  Qed.
End LMN.
