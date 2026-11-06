(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK00 YK0s YK18 YN02 YQ0j YQ0b YK05 YA0i YA0l YA0e YG00 YG01 YG0m YG0h YG10 YG0u YG0d YCcz YB1u YCrd YF9i YF9j YD1p YD1v YD1q YD2d YD2b YD1r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YD1f YCrc.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0p YG0r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Definition lib_site_rgb : Prop :=
forall ly S (W : world trbsegs) (regs : bvmap 5 word) mem md p n,
lib_pre B ly S W regs mem md ->
getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB   -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
frm_zero fp_csr ->
SRr trbsegs W (cfg_at trbsegs A_LLVMF regs mem md)
(fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@mkst fx' regs' (w64 RA_LLVMF) mem' (seg_rom trbsegs)) md' /\ frm_zero (@fp_csr fx') /\
ajournal trbsegs B LLVMF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_RLIB /\
aregs_preserved regs regs' /\ getr regs' 10%bv = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
bud_le S S' EV_RLIBV CN_RLIB WT_RLIB HL_RLIB).
Theorem trb_rlib_site_fx : trb_rlibV_contract B -> lib_site_rgb.
Proof.
intros LIBC ly S W regs mem md p n HPRE R10 R11 Hpn Hfr Hev Hlive Hro Hfrm.
pose proof HPRE as (HAR & Hret & Hra & Hgp & Htp & Hal & [Wlo Whi] & [Tlo Thi] & Elo & Ehi & Hpres & Hs0 & Hqt).
pose proof (layout_of_AR B _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
apply (LIBC ly S W regs mem md p n); try assumption.
split; [exact HAR|]. split; [exact Hret|]. split; [rewrite Hra; unfold RA_LLVMF; lia|]. split; [exact Hgp|]. split; [exact Htp|].
split.
- unfold astk_ok. rewrite Ehi. unfold ly_bot, kHighMemEnd, LLVMF_STK, ASTACK, kStackSpan in *. repeat split; lia.
- split; [exact Hpres|]. split; [| exact Hqt]. apply achain_low. exact Hs0.
Qed.
End b.
End a.
Theorem trb_rlib_site {rc : YN05.RunCeil} (B : asyms) : trb_rlibV_contract_all B -> forall fx : YK11.FPState, @lib_site_rgb fx rc B.
Proof. intros LIBC fx. apply (@trb_rlib_site_fx fx rc B). apply LIBC. Qed.
