(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD26.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build; ml_malloc gets the trace's length (tr_admit_len) instead of its membership in the universe (C5 model laws); m1_common gives its continuation stk_top (AD1v.v) after the malloc whenever it held before, and the file arm carries it, with frm0, to rd0_file; lia's euclidean-division flag is set Local (the file exports no setting). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AD26.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD26.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the auxv layout over the CONFIG_RSEQ flag; the launch's ProcInput). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK00 YK14 YK15.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01 YG0k YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AD1v_w AD1y_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma img_regions_wf : regions_wf IMG_REGIONS = true. Proof. reflexivity. Qed.
Lemma submem_refl : forall rs, submem rs rs.
Proof. induction rs as [|r rs IH]; [constructor|]. apply submem_keep; [|exact IH]. repeat split; try lia. auto. Qed.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section c.
Section M1.
Variables (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte) (rnd : EntryDraw).
#[local] Notation efn := (in_execfn inp).
(* [YP08.E0] is TOP-anchored and launch-indexed at 75d69e00 (YP08.v:209-210): entry-draw top,
   the run's own [kb_rseq] flag, and the execfn. *)
#[local] Notation EL := (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) [a0; p] (in_envp inp) (in_execfn inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Lemma EL0 : bv_unsigned (ew EL 0) = usp. Proof. reflexivity. Qed.
End M1.
End c.
