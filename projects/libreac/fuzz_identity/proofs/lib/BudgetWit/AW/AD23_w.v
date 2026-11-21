(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD23.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD23.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed REFUSED, Hva, EL, eagree, HR0, E3_0 and 1 more; added Hargv, Hvl, Hlau, Hvi, efn). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YL0a YL0b YL09 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD1y_w AD20_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD1v_w AD26_w AD24_w AD21_w AD25_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma blocks_bytes_blocks : forall s, blocks_bytes s = fold_right (fun b acc => snd b + acc) 0 (blocks s).
Proof.
intros s. unfold blocks_bytes, blocks. induction (st_chunks s) as [|k ks IH]; cbn; [reflexivity|].
destruct (is_alloc k); cbn; rewrite IH; reflexivity.
Qed.
Lemma pow2_double_le : forall cap e, 0 <= e -> cap = 2 ^ e -> cap < 2 ^ 26 -> 2 * cap <= 2 ^ 26.
Proof.
intros cap e He -> Hlt. assert (e < 26) by (apply (Z.pow_lt_mono_r_iff 2); lia).
replace (2 * 2 ^ e) with (2 ^ (e + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia.
Qed.
Lemma denot_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma runs_at_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) usp R,
(forall a, usp <= a < 2 ^ 64 -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> sp_window_lo <= usp ->
runs_at usp (mrestrict H m) R -> runs_at usp (mrestrict H' m') R.
Proof.
intros H H' m m' usp R HA Husp HR. unfold sp_window_lo in Husp. unfold runs_at in HR |- *. apply Forall_forall. intros [a bs] Hab.
pose proof (proj1 (Forall_forall _ _) HR _ Hab) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
split; [exact Q1|]. split; [exact Q2|]. intros j Hj. pose proof (Q3 j Hj) as Q.
pose proof (mbyte_of_aview tfibsegs _ _ _ _ _ (HA (a + Z.of_nat j) ltac:(lia))) as X. unfold mbyte in X.
rewrite (seg_rom_none tfibsegs (a + Z.of_nat j)) in X by first [lia | apply not_in_img_high; lia].
rewrite Q in X. destruct (nth_error bs j) as [b|] eqn:En; [| apply nth_error_None in En; lia].
destruct (mrestrict H' m' (Z_to_bv 64 (a + Z.of_nat j))); congruence.
Qed.
Lemma blk_of_frame_r : forall H E rs (m m' : word -> option byte) buf len data usp,
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
sp_window_lo <= usp -> (forall a, buf <= a < buf + len -> ~ in_img tfibsegs a) -> 0 <= buf -> buf + len <= usp - 65536 ->
blk H m buf len data -> blk H m' buf len data.
Proof.
intros H E rs m m' buf len data usp HF Hok E0 Husp Hni Hb0 Hhi HB i Hi. pose proof (u64_range (ew E 0)) as R0. rewrite E0 in R0.
rewrite <- (HB i Hi). apply HF. intros Hw. apply (in_wrange_drv E rs _ Hok) in Hw. rewrite u64_lit in Hw by (unfold sp_window_lo in Husp; lia).
destruct Hw as [Hw|Hw]; [unfold sp_window_lo in Husp; lia |]. apply DRVW_rw in Hw. apply (Hni (buf + i) ltac:(lia)). apply in_img_rw. lia.
Qed.
Section Gr.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MSITE : malloc_site_tfa B.
Hypothesis MCPY : memcpy_site_tfa B.
Hypothesis FREE : free_site_tfa B.
Hypothesis REFUSED : refused_leaf_tfa B.
Variables (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte) (rnd : EntryDraw).
(* Shape copied from the in-tree ported donor AD1v_w.v:121-127 / YL0q.v Section b: binders
   [sp brk mbase] .. [inp] .. [a0 p] .. [rnd], premises
   [valid_sp; in_argv =; valid_argv (in_argv inp); valid_envp; valid_launch;
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp; valid_input].
   [Hargv] is new here: [AD25_w.eagree_6] needs it to turn YP08's [in_argv inp] back into
   [[a0; p]].  [entry_stack_fits] is NOT added: [entry_launch_ok_va] implies it
   ([entry_launch_ok_va_fits], 75d69e00 Run.v:3718-3722), and this section never had it. *)
Hypothesis Hargv : in_argv inp = [a0; p].
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
(* [AD25]'s Section-f exports gained [rnd] immediately after [p]; [eagree] is one of them. *)
#[local] Notation eagree := (AD25_w.eagree sp inp xw xd a0 p rnd).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Definition gvals (E : YP0m.env) (buf cap : Z) : Prop :=
bv_unsigned (ew E A_BUF) = buf /\ bv_unsigned (ew E A_CAP) = cap /\ 0 <= bv_unsigned (ew E A_LEN) /\ 1 <= bv_unsigned (ew E A_N)
/\ bv_unsigned (ew E A_LEN) + bv_unsigned (ew E A_N) = cap /\ 65536 <= cap <= 2 ^ 26.
Section f.
Variables (E3 : YP0m.env) (W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate)
(pth : list byte) (data : list byte) (pb : sptr) (buf cap : Z).
Hypothesis HE3 : eagree E3.
Hypothesis HSG : st_ok tfibsegs E3 S_G (restrict (w_H W) ms).
Hypothesis G : gvals E3 buf cap.
Hypothesis HAR0 : AR tfibsegs B ly S W (ms_mem ms) md.
Hypothesis HAI0 : AI tfibsegs (w_H W) (w_A W) md.
Hypothesis HTOP : top_ok usp ly.
Hypothesis Hbl : blocks S = [(pb, cap)].
Hypothesis Hpb : sptr_addr B ly pb = buf.
Hypothesis Hnev : st_nev S + 2 <= EV_MAX.
Hypothesis HR0 : runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp (ed_top rnd) [a0; p] envp efn).
Hypothesis Hfds0 : m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 cap)).
Hypothesis Hfs0 : m_fs md = in_fs inp.
Hypothesis HFI0 : FINV ly (w_H W) (ms_mem ms).
Let E3_0 : bv_unsigned (ew E3 0) = usp. Proof. exact (eagree_0 sp inp xw xd a0 p rnd E3 HE3). Qed.
(* [eagree_6] is the one AD25 export that goes through [YP08.z_rand_end], so it alone picks
   up [brk mbase] and the four launch hypotheses as well as [rnd]. *)
Let E3_6 : usp <= bv_unsigned (ew E3 6).
Proof. exact (eagree_6 sp brk mbase inp xw xd a0 p rnd Hargv Hsp Hva Hve Hvl Hlau E3 HE3). Qed.
Let HCT : YM05.ceil_of_top (usp - stack_max_size). Proof. exact (top_ok_ceil _ _ HTOP). Qed.
End f.
End Gr.
End c.
