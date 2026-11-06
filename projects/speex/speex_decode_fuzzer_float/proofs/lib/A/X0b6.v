(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05q X05s X05u X05t
X081 X05l X05m X09f X06d X069 X082 X08y X0b1 X0b0 X05a X088.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bc X0bb.
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

Theorem sbl_subframe : sb_subframe_cps RT.
Proof.
intros X PMc mR sub b sm FDO MST IH SUB SM.
assert (HM : sbd_mode (x_s X) = ModeWB \/ sbd_mode (x_s X) = ModeUWB)
by (destruct IH as [_ _ _ _ _ _ IINV _]; destruct IINV as (HMO & _); exact HMO).
destruct HM as [HM | HM].
- exact (sbl_subframe_wb RT AF AF_LIB APO AUN AUNlo MEMS L2L8 INNV X PMc mR sub b sm FDO MST IH SUB SM HM).
- exact (sbl_subframe_uwb RT AF AF_LIB APO AUN AUNlo MEMS L2L8 INNV X PMc mR sub b sm FDO MST IH SUB SM HM).
Qed.
End SBL.
