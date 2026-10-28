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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_bcall Sj_num_laf Sj_num_lm_kit Sj_num_lm_runs3 Sj_num_lm_defs Sj_num_lm_n.
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

Section LMC.
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
  Notation lm_norm := (lm_norm sp gp tp F fc X lo d spq f len0 ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YL SHPY BCP L0 Q KEXIT).
  Notation lm_f858 := (lm_f858 sp gp tp F fc X lo d spq f len0 ybs m0 SPQ ROOM TOP F64 FLO FSH FS0 X8 XR XSH XS0 SEP YL SHPY BCP L0 Q KEXIT).

  Variable j : Z.
  Hypothesis Hj : (1 <= j < 5)%Z.

  Hypothesis KJ : forall xra xt0 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 a0 a96 a104 zsh ziw (mm : mem) len, (j + 1 < 5)%Z ->
    LMINV (lm_spillL X f zl a0 a96 a104) zsh ziw mm len False -> (CAPL -> len <= zl + (j + 1) + 1)%Z ->
    evt bsegs Q (LJ 0xed480 (j + 1) xra xt0 (Z_to_bv 64 5) xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 Y) xs11 xt3 xt4 xt5 xt6 mm).

  Lemma lm_2f8 : forall xra xt0 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 a0 a96 a104 zsh ziw (mm : mem) len,
    LMINV (lm_spillL X f zl a0 a96 a104) zsh ziw mm len False -> (CAPL -> len <= zl + j + 2)%Z ->
    evt bsegs Q (LJ 0xed378 j xra xt0 (Z_to_bv 64 5) xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 (Z_to_bv 64 Y) xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT Hj KJ.
    intros until len. intros INV HB. pose proof INV as INV0. lm_open INV0. lm_env. pose proof Hj as Hj'.
    num_cur_mem ltac:(fun m1 => eapply (lm_run2 f m1 ltac:(lia) Q); [exact ZSH | exact MI | apply munch_refl | apply wmono_refl |];
      clear MI ZSH; intros zsh' mm' ZSH MI MU' WM'; transport_after_call bsegs m1 mm' MU' WM'; clear MU' WM').
    assert (INV1 : LMINV (lm_spillL X f zl a0 a96 a104) zsh' ziw mm' len False) by lm_close.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xed27c%Z => first [ eapply evt_eq; [| eapply lm_norm]; [num_st_eq | exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      | 0xed480%Z => first [ eapply evt_eq; [| eapply KJ]; [num_st_eq | lia | exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma lm_2dc : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 a0 a96 a104 (mm : mem) len zl',
    LMINV (lm_spillL X f zl a0 a96 a104) (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 zl') mm len False -> (0 <= zl' <= 62)%Z -> (zl' <= zl + 1)%Z -> (CAPL -> len <= zl + j + 1)%Z ->
    evt bsegs Q (LJ 0xed35c j xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 (Z_to_bv 64 Y) xt3 xt4 xt5 xt6 mm).
  Proof using LMH KEXIT Hj KJ.
    intros until zl'. intros INV Hz Hz1 HB. pose proof INV as INV0. lm_open INV0. lm_env. pose proof Hj as Hj'.
    bwalk ltac:(fun pc => lazymatch pc with | 0xedbc4%Z => idtac end).
    pose proof ZIA as [ZIB _].
    pose proof (bytes_at_sub bsegs mm (f + 608) zibs 0 (Z.to_nat (8 * zl')) ZIB ltac:(lia)) as YB2.
    change (skipn 0 zibs) with zibs in YB2. change (Z.of_nat 0) with 0%Z in YB2. replace (f + 608 + 0)%Z with (f + 608)%Z in YB2 by lia.
    pose proof (BCP _ MU WM) as GC.
    pose proof (zero_run_of_CB _ _ _ ZSH) as ZRI.
    replace (f / 8 + 2147450956)%Z with ((f + 608) / 8 + 2147450880)%Z in ZRI by (replace (f + 608)%Z with (f + 8 * 76)%Z by lia; rewrite (f64_div f 76 F64); lia).
    eapply evt_cut.
    { eapply evt_eq; [| eapply lafb_spec with (X := X) (Y := (f + 608)%Z) (ny := zl') (st := j) (lo := lo) (len := len) (bs := bs) (ybs := firstn (Z.to_nat (8 * zl')) zibs)];
        [num_st_eq | ..]; rewrite ?unsigned_lit by lia; unfold LAFB_STACK;
        [ lia | lia | lia | rewrite length_firstn; lia | lia | lia | lia | Z.div_mod_to_equations; lia | exact X8 | lia | lia
        | exact (shzp_zr [((spq - 80)%Z, spq); (X, (X + 498)%Z)] mm X 63 ZR X8 ltac:(lia) ltac:(intros a Ha; cbn [outside]; change (Z.of_nat 63) with 63%Z in Ha; split; [lia|]; split; [lia| exact I]))
        | intros m' MU' WM'; eapply shz_sub;
          [ exact (shzp_zr [((spq - 80)%Z, spq); (X, (X + 498)%Z)] mm (f + 608)%Z 63 ZRI ltac:(Z.div_mod_to_equations; lia) ltac:(lia)
                     ltac:(intros a Ha; cbn [outside]; change (Z.of_nat 63) with 63%Z in Ha; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]) m' MU' WM') | lia | lia ]
        | exact MI | exact ST | exact GC | exact XA | exact XL | exact XN | lia | exact YB2 ]. }
    cbv beta. intros ms' P. unfold lafb_post in P.
    destruct P as (? & ? & ? & r0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & bs3 & len3 & -> & MUc & WMc & MIc & STc & XA3 & XL3 & XN3 & LEN3 & G).
    rewrite ?unsigned_lit in MUc, STc by lia. unfold LAFB_STACK in MUc.
    assert (G' : (CAPL -> bv_unsigned r0 = 1 /\ len3 <= zl + j + 2)%Z).
    { intros HC. unfold lafb_G in G. destruct (G ltac:(lia) ltac:(lia)) as (-> & G1 & _). rewrite unsigned_lit by lia. lia. }
    clear G. clear XA XN YB2 GC ZRI NB.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call bsegs mo mn MUc WMc end.
    clear MUc WMc MI. rename MIc into MI. rename STc into ST.
    num_ret_pc.
    assert (INV1 : LMINV (lm_spillL X f zl a0 a96 a104) (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 zl') m3 len3 False) by lm_close.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xedb58%Z => u_trap pc
      | 0xed8d8%Z => first [ eapply lm_f858; [exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      | 0xed378%Z => first [ eapply evt_eq; [| eapply lm_2f8]; [num_st_eq | exact INV1 | intros HC; lia] | fail 100 "cut" pc ]
      end).
  Qed.
End LMC.
