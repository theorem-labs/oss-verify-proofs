(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1w.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build; lib_site_x takes the call index j, GI_cmdA j before the call and GI_cmdA (j + 1) after it (lib/A/Prog/CmdGlob.v), the program's statics cmd_PG join the call's footprint, the pre-condition asks for the stack from sp to the stack top present (astack_pres) and rounding mode 0 (frm = fcsr bits 5..7), and the call returns in a float state fx' that keeps every float register but fa0 and either keeps fcsr or keeps frm = 0 (C3's pass 5b form); post_P_tfa, run_Q_tfa and loop_L_x carry stk_top and frm0 (AD1v.v). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AD1w.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1w.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK00 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition STDOUT_MUT (a : Z) : Prop := (STDOUT_LO <= a < STDOUT_HI) \/ (SOBUF_LO <= a < SOBUF_HI).
Definition stdout_img (H : word -> bool) (m : word -> option byte) : Prop :=
forall a, STDOUT_LO <= a < STDOUT_HI -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Definition xst_frame_tfa : Prop :=
forall k (H H' : word -> bool) (m m' : word -> option byte),
xst k H m -> (forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> xst k H' m'.
End c.
