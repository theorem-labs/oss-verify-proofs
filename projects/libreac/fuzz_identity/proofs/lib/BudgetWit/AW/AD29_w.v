(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD29.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD29.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed so_not_owned, Hargv, Hva, EL, EL6; added Hvl, Hlau, Hvi, efn). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD1y_w AD26_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD25_w AD2h_w AD1w_w AD2f_w AD1s_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.

From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD1y_w AD26_w AD24_w.

From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD21_w AD25_w AD23_w AD2h_w AD1w_w AD2f_w AD2b_w AD2g_w AD1s_w.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis FREE : free_site_tfa B.
Hypothesis EXITL : exit_leaf_tfa B xst.
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

Lemma so_not_owned : forall ly S W mem md a, AR tfibsegs B ly S W mem md -> STDOUT_MUT a -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a HAR Ha X.
assert (Hi : in_img tfibsegs a) by (apply in_img_rw; unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia).
pose proof (proj1 (al_owned_image _ _ ARL _ _ _ _ _ _ HAR Hi) X) as Y. rewrite (ts_owned B HB) in Y.
apply Exists_exists in Y as ([lo l] & Hin & Hz). unfold in_zr in Hz. cbn in Hz.
unfold Tfib_owned_static in Hin. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. cbn in Hin.
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|]). exact Hin.
Qed.
Variables (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte) (rnd : EntryDraw).
Hypothesis Hargv : in_argv inp = [a0; p].
(* Shape copied from the in-tree ported donor AD1v_w.v:121-127 / YL0q.v Section b: binders
   [sp brk mbase] .. [inp] .. [a0 p] .. [rnd], premises
   [valid_sp; in_argv =; valid_argv (in_argv inp); valid_envp; valid_launch;
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp; valid_input].
   [entry_stack_fits] is not added: [entry_launch_ok_va] implies it
   ([entry_launch_ok_va_fits], 75d69e00 Run.v:3718-3722), and this section never had it.
   [Hva] matches YP08's input-indexed validity hypothesis (YP08.v:493). *)
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
(* [YP08.E0] is TOP-anchored and launch-indexed at 75d69e00 (YP08.v:209-210): entry-draw top,
   the run's own [kb_rseq] flag, and the execfn. *)
#[local] Notation EL := (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) [a0; p] (in_envp inp) (in_execfn inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.

Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp (kb_rseq (in_kernel inp)) [a0; p] envp)).
assert (Hz : z_rand usp (kb_rseq (in_kernel inp)) (in_argv inp) envp + 16 < 2 ^ 63)
by (eapply (YP08.z_rand_end TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau)).
rewrite Hargv in Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Definition at_rs (rs : smem) (ss' : sstate) (E : YP0m.env) (W : world tfibsegs) (mem0 : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs E ss' (restrict (w_H W) ms')
/\ frame_of E rs mem0 (ms_mem ms')
/\ frame_of E rs (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms')).
End c.
End b.
