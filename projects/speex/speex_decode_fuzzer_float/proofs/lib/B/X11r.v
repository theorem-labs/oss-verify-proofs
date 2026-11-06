(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X07z.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm
X0ys X0x2 X0yt X0zq X11l X11k X0w7 X0yz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0w7 X0yz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X11t X11s X11z X11y.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Section SBL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis AUNlo : allocas_unpoison_lo_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis L2L8 : lsp_to_lpc_cps8 RT.
Hypothesis INNV : forall p, scb_params_ok p -> innov_unquant_cps RT (ptr := bptr) (InnovSplitCbShapeSignUnquant p).

Theorem sblB_subframe : sb_subframe_cps RT.
Proof.
intros X PMc mR sub b sm FDO MST IH SUB SM.
pose proof (sblB_dA RT AF AF_LIB APO AUN MEMS INNV) as DA.
assert (HM : sbd_mode (x_s X) = ModeWB \/ sbd_mode (x_s X) = ModeUWB)
by (destruct IH as [_ _ _ _ _ _ IINV _]; destruct IINV as (HMO & _); exact HMO).
destruct HM as [HM | HM].
- exact (sblB_subframe_wb RT AF AF_LIB APO AUNlo MEMS L2L8 DA X PMc mR sub b sm FDO MST IH SUB SM HM).
- exact (sblB_subframe_uwb RT AF AF_LIB APO AUNlo MEMS L2L8 DA X PMc mR sub b sm FDO MST IH SUB SM HM).
Qed.
End SBL.
