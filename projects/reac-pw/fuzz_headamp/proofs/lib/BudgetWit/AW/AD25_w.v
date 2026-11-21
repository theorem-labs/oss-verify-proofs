(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD25.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AD25.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AD25.v (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD25.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_pw.fuzz_headamp.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YL0a YL0b YL09 YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG01 YG0f YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD1y_w AD20_w AD1v_w AD26_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section e. Context {fx : YK11.FPState}.
Section Rd.
Lemma wvb_fs' : forall l mat (m : Model), m_fs (with_vm_backing l mat m) = m_fs m.
Proof. intros l mat m. destruct m; reflexivity. Qed.
Lemma wvb_fds' : forall l mat (m : Model), m_fds (with_vm_backing l mat m) = m_fds m.
Proof. intros l mat m. destruct m; reflexivity. Qed.
Lemma apresent_some' : forall (H : word -> bool) mem a, apresent H mem a -> mem (Z_to_bv 64 a) <> None.
Proof. intros H mem a [_ [bb Hb]]. rewrite Hb. discriminate. Qed.
Section f.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Definition at_st (ss ss' : sstate) (E : YP0m.env) (W : world tfibsegs) (mem0 : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs E ss' (restrict (w_H W) ms')
/\ frame_of E (ss_mem ss) mem0 (ms_mem ms')
/\ frame_of E (ss_mem ss) (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms')).
End f.
End Rd.
End e.
