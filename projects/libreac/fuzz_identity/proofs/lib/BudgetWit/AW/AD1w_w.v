(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1w.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed B, ELV, tail_at, short_leaf_tfa, overrun_leaf_tfa, post_P_tfa); the channel reader that fdchan asks for at LPS 727298f3 carried beside the descriptor fact, from cs_ok's co_rdr. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK00 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
(* [YP08.E0] is TOP-anchored and launch-indexed at 75d69e00 (YP08.v:209-210): entry-draw top,
   the run's own [kb_rseq] flag, and the execfn.  Every Prop below therefore carries the draw.
   Shape copied from the in-tree ported donor AD1v_w.v:33-34 / YL0q.v Section b: binders
   [sp brk mbase] .. [inp] .. [a0 p] .. [rnd], premises
   [valid_sp; in_argv =; valid_argv (in_argv inp); valid_envp; valid_launch;
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp; valid_input].
   [entry_stack_fits] is DROPPED rather than kept: it is implied by [entry_launch_ok_va]
   ([entry_launch_ok_va_fits], 75d69e00 Run.v:3718-3722).  MEASURED: this file consumed it
   nowhere -- grep for [entry_stack_fits] over AD1w_w.v returns no hit.  Firing control for
   that zero: the same query fires on AD2i_w.v:264 and AD2i_w.v:754, two genuine direct
   consumptions, in a section that is not one of these Props. *)
#[local] Notation ELV sp rnd a0 p inp xw xd :=
(YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) [a0; p] (in_envp inp) (in_execfn inp) xw xd).

Definition tail_at (ss : sstate) (E : YP0m.env) (sp : word) (inp : ProcInput) (a0 p data : list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (pb : sptr) (cap : Z) : Prop :=
st_ok tfibsegs E ss (restrict (w_H W) ms) /\
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb /\ bv_unsigned (ew E A_LEN) = dlen data /\
(* [runs_main_tfa] is SIX-argument at 75d69e00 (AD2i_w.v:148): it gained the entry-draw top and
   the execfn.  [tail_at] is handed WHOLE to lemmas in six files this lane does not own
   (AD27, AD2b, AD2c, AD2d, AD2e, AD2g), so per the Section rule the new value is quantified
   EXISTENTIALLY here instead of becoming a fourteenth parameter: the arity is unchanged and
   every one of those call sites still typechecks.  Providers have the draw in hand, so the
   witness is free; consumers that merely re-frame the fact ([AD2g]) [destruct] and re-[exists].
   MEASURED that no consumer needs the concrete draw: in AD27's [fw_leaf] (AD27_w.v:791-796)
   this conjunct is bound as [HR] and never used again in the proof body.  Firing control for
   that zero: the same scan over the same body finds [HAR], [HTOP] and [HFI] used repeatedly. *)
(exists rnd : EntryDraw, runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) [a0; p] (in_envp inp) (in_execfn inp))) /\
AI tfibsegs (w_H W) (w_A W) md /\ AR tfibsegs B ly S W (ms_mem ms) md /\ top_ok (bv_unsigned sp) ly /\
blocks S = [(pb, cap)] /\ st_nev S <= 64 /\ 65536 <= cap <= 2 ^ 26 /\ dlen data < cap /\
blk (w_H W) (ms_mem ms) (sptr_addr B ly pb) (dlen data) data /\
m_fs md = in_fs inp /\ m_fds md = APSG.fds_std /\ drv_minv S cap (dlen data) /\
(* LAST conjunct, beside the descriptor fact: [fdchan] at LPS 727298f3 asks for the
   model's channel reader as well, and every leaf below this one writes to a channel.
   It comes from the hand-off, where [cs_ok]'s [co_rdr] proves it. *)
FINV ly (w_H W) (ms_mem ms) /\ m_channel_reader md = true    .

Definition short_leaf_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z)
(rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> dlen data <= 5 ->
tail_at S_SHORT (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag msg_short (in_fs inp)).

Definition overrun_leaf_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z)
(rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 <= dlen data < 6 + config_len data ->
tail_at S_OVR (edset (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag msg_overrun (in_fs inp)).

Definition post_P_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z)
(rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
tail_at S_P (edset (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition STDOUT_MUT (a : Z) : Prop := (STDOUT_LO <= a < STDOUT_HI) \/ (SOBUF_LO <= a < SOBUF_HI).
Definition stdout_img (H : word -> bool) (m : word -> option byte) : Prop :=
forall a, STDOUT_LO <= a < STDOUT_HI -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Definition xst_frame_tfa : Prop :=
forall k (H H' : word -> bool) (m m' : word -> option byte),
xst k H m -> (forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> xst k H' m'.
Definition A_EXIT : Z := 0x8a6fc.
Definition exit_leaf_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs) (code : Z) (k : nat),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 code -> (code = 0 \/ code = 2) -> spZ regs = usp - 48 ->
getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_L ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) ->
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) -> m_channel_reader md = true -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 A_EXIT) mem (seg_rom tfibsegs)) md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
End c.
