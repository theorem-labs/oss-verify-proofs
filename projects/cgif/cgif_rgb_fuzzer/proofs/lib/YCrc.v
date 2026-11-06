(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe8 YCe9 YCi1 YCie YCph
YCrr YCrd.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition EV_RLIB : Z := EV_RGBNEWGIF + 16 * (EV_RRFC + EV_RGBADD + 1) + EV_RGBCLOSE.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition trb_rlib_post (B : asyms) (regs : bvmap 5 word) ly S (W : world trbsegs) mem md : world trbsegs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@mkst fx' regs' (w64 RA_LLVMF) mem' (seg_rom trbsegs)) md' /\ frm_zero (@fp_csr fx') /\
ajournal trbsegs B LLVMF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_RLIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S).
Definition trb_rlib_contract (B : asyms) : Prop :=
forall ly S (W : world trbsegs) (regs : bvmap 5 word) mem md p n,
afn_pre trbsegs B LLVMF_STK ly S W regs mem md [] ->
raZ regs = RA_LLVMF ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> vev S + EV_RLIB <= VEV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
frm_zero fp_csr ->
SRr trbsegs W (cfg_at trbsegs A_LLVMF regs mem md) (trb_rlib_post B regs ly S W mem md).
Definition trb_rlibV_post (B : asyms) (regs : bvmap 5 word) ly S (W : world trbsegs) mem md : world trbsegs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@mkst fx' regs' (w64 RA_LLVMF) mem' (seg_rom trbsegs)) md' /\ frm_zero (@fp_csr fx') /\
ajournal trbsegs B LLVMF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_RLIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
bud_le S S' EV_RLIBV CN_RLIB WT_RLIB HL_RLIB.
Definition trb_rlibV_contract (B : asyms) : Prop :=
forall ly S (W : world trbsegs) (regs : bvmap 5 word) mem md p n,
afn_pre trbsegs B LLVMF_STK ly S W regs mem md [] ->
raZ regs = RA_LLVMF ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview trbsegs (w_H W) mem) ->
frm_zero fp_csr ->
SRr trbsegs W (cfg_at trbsegs A_LLVMF regs mem md) (trb_rlibV_post B regs ly S W mem md).
End a.
Definition trb_rlib_contract_all {rc : YN05.RunCeil} (B : asyms) : Prop :=
forall fx : YK11.FPState, @trb_rlib_contract fx rc B.
Definition trb_rlibV_contract_all {rc : YN05.RunCeil} (B : asyms) : Prop :=
forall fx : YK11.FPState, @trb_rlibV_contract fx rc B.
