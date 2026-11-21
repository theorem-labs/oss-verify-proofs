(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD29.v, with its module paths changed, names TfibSyms -> GrantSyms. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/A/AD29.v (donor image sha256 c2c7559b29bd), with its module paths changed, names GrantSyms -> UciSyms. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD29.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD1y_w AD26_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import AD25_w AD2h_w AD1w_w AD2f_w AD1s_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section b. Context {fx : YK11.FPState}.
Section c.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Definition so_state (k : nat) (H : word -> bool) (m : word -> option byte) : Prop :=
(k = 0%nat /\ stdout_img H m) \/ ((1 <= k)%nat /\ xst k H m).
Lemma so_state_keep : forall k H H' m m',
(forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> so_state k H m -> so_state k H' m'.
Proof.
intros k H H' m m' HA [[Hk HI]|[Hk HX]]; [left | right]; split; try assumption.
- intros a Ha. rewrite (HA a) by (left; exact Ha). apply HI. exact Ha.
- exact (XFR k H H' m m' HX HA).
Qed.
Definition at_rs (rs : smem) (ss' : sstate) (E : YP0m.env) (W : world tfibsegs) (mem0 : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs E ss' (restrict (w_H W) ms')
/\ frame_of E rs mem0 (ms_mem ms')
/\ frame_of E rs (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms')).
End c.
End b.
