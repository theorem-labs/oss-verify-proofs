(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e YI08 YI0c UI3h UI3d
UI39 UI2p UI26 UI57 UI58 UI4y UI55 UI4z UI51 UI53 UIZg
UO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis NEWG : rgb_newgif_spec API.
Hypothesis CLOSE : forall fx', rgb_close_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', rgb_addframe_spec (fx:=fx') API.
Lemma rlh_case_5 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
14 <= n -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
ubs2_rgb_rodata_ok mem ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid HRO G10 G11.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr). destruct Hst as (Hal16 & _).
assert (Hn0 : 0 < n) by lia.
eapply SR_bind; [exact (rl_header API IMG L A regs mem md p n HPRE G10 G11 (or_intror (conj Hn0 Hpn))) |].
intros c' HP. unfold rl_hdr_post in HP.
destruct HP as (regs1 & memc & HJ & HSV & G2 & HRU & [(Hlt & _) | (Hge & -> & attr & gen & loops & Wv & Hv & HW & HHv & Wp & Wn & W14 & Hobj)]); [lia |].
exact (rl_main API IMG NEWG CLOSE ADDF L A mem md regs regs1 L A memc md p n Wv Hv attr gen loops
  HFZ HJ Hid Hra Htp Hal16 HRO (fun b Hb => Hb) Hpn HC HW HHv HSV Wp Wn W14 Hobj G2 HRU).
Qed.
Lemma rlh_case_4 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
12 <= n <= 13 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr). destruct Hst as (Hal16 & _).
assert (Hn0 : 0 < n) by lia.
eapply SR_bind; [exact (rl_header API IMG L A regs mem md p n HPRE G10 G11 (or_intror (conj Hn0 Hpn))) |].
intros c' HP. unfold rl_hdr_post in HP.
destruct HP as (regs1 & memc & HJ & HSV & G2 & HRU & [(Hlt & ->) | (Hge & _)]); [| lia].
exact (rl_ret0 API IMG L A mem md regs regs1 L A memc md HFZ HJ Hid Hra Hal16 (fun b Hb => Hb) HSV G2 HRU).
Qed.
Lemma rlh_case_3 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
8 <= n <= 11 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr). destruct Hst as (Hal16 & _).
assert (Hn0 : 0 < n) by lia.
eapply SR_bind; [exact (rl_header API IMG L A regs mem md p n HPRE G10 G11 (or_intror (conj Hn0 Hpn))) |].
intros c' HP. unfold rl_hdr_post in HP.
destruct HP as (regs1 & memc & HJ & HSV & G2 & HRU & [(Hlt & ->) | (Hge & _)]); [| lia].
exact (rl_ret0 API IMG L A mem md regs regs1 L A memc md HFZ HJ Hid Hra Hal16 (fun b Hb => Hb) HSV G2 HRU).
Qed.
Lemma rlh_case_2 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
4 <= n <= 7 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr). destruct Hst as (Hal16 & _).
assert (Hn0 : 0 < n) by lia.
eapply SR_bind; [exact (rl_header API IMG L A regs mem md p n HPRE G10 G11 (or_intror (conj Hn0 Hpn))) |].
intros c' HP. unfold rl_hdr_post in HP.
destruct HP as (regs1 & memc & HJ & HSV & G2 & HRU & [(Hlt & ->) | (Hge & _)]); [| lia].
exact (rl_ret0 API IMG L A mem md regs regs1 L A memc md HFZ HJ Hid Hra Hal16 (fun b Hb => Hb) HSV G2 HRU).
Qed.
Lemma rlh_case_1 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
2 <= n <= 3 -> In (p, n) (blocks L A) ->
frm_zero fp_csr ->
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC Hpn HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr). destruct Hst as (Hal16 & _).
assert (Hn0 : 0 < n) by lia.
eapply SR_bind; [exact (rl_header API IMG L A regs mem md p n HPRE G10 G11 (or_intror (conj Hn0 Hpn))) |].
intros c' HP. unfold rl_hdr_post in HP.
destruct HP as (regs1 & memc & HJ & HSV & G2 & HRU & [(Hlt & ->) | (Hge & _)]); [| lia].
exact (rl_ret0 API IMG L A mem md regs regs1 L A memc md HFZ HJ Hid Hra Hal16 (fun b Hb => Hb) HSV G2 HRU).
Qed.
Lemma rlh_case_0 : forall L A (regs : bvmap 5 word) mem md (p n : Z),
0 <= n <= 1 ->
frm_zero fp_csr ->
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rllvm_post API regs L A mem md).
Proof.
intros L A regs mem md p n HC HFZ HPRE Hid G10 G11 Hp64.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr). destruct Hst as (Hal16 & _).
eapply SR_bind; [exact (rl_header API IMG L A regs mem md p n HPRE G10 G11 (or_introl (conj HC Hp64))) |].
intros c' HP. unfold rl_hdr_post in HP.
destruct HP as (regs1 & memc & HJ & HSV & G2 & HRU & [(Hlt & ->) | (Hge & _)]); [| lia].
exact (rl_ret0 API IMG L A mem md regs regs1 L A memc md HFZ HJ Hid Hra Hal16 (fun b Hb => Hb) HSV G2 HRU).
Qed.
End S.
End d.
