(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACe6.v. *)
(* The contract of ctrl_lay_block (0x82ffc) on fuzz_grant's ASan build — the
   statement only; the walk that proves it is CtrlLayBlock.v. A caller Requires
   this file and takes `tctrl_lay_block_spec` as a Section hypothesis, so its
   own file does not depend on the walk.

   It is stated for the one call the program makes: reac_ctrl_stamp_headamp
   passes the static control-frame row CTRL_FRAMES[CTRL_HEADAMP] (A_OBJ 18 =
   0x9c670, byte +2 = 2 = BLOCK_TMPL) and a null model pointer, so the jump
   table at A_OBJ 24 = 0x20ff4 sends the walk to the template case and the call
   of reac_box_model_block at 0x8322c is not reached. The call writes the
   caller's 32 bytes [p+18, p+50), so the contract is in cgif's caller-journal
   form (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365); tcj_kept, twr_ok and
   tsrc_ok are CtrlFinish.v's. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantBase CtrlFinish.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
(* The image objects the walk names; A_ROW is CtrlFinish.v's. *)
Definition A_JT : nat := 24%nat.       (* the switch's jump table,   0x20ff4, 10 entries *)
Definition ROW_BYTES : Z := 24.
(* The stack each call needs: its own frame (128) plus the 32 bytes the
   `andi sp,sp,-32` at 0x83038 may drop, plus the runtime's own ESTACK. *)
Definition TLAY_STK : Z := 160 + ESTACK.
Definition EV_LAY : Z := 0.
Section e.
Variable B : asyms.
Definition tlay_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (p ch pm v : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
(exists f, S2 = set_fs f Sc) /\
garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18) (lay_z ch pm v) /\
tcj_kept B TLAY_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => p + 18 <= a < p + 50).
Definition tctrl_lay_block_spec (a : Z) (rlo rhi : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p g ch pm v : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS rlo rhi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 p -> getr regs 11 = w64 (VAL (A_OBJ A_ROW)) -> getr regs 12 = w64 0 -> getr regs 13 = w64 g ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TLAY_STK -> spZ regs <= sp0 ->
Z.of_nat (length (frames Sc)) <= 9 ->
(* the 32 bytes it lays down *)
0 <= p -> p + 50 <= 2 ^ 47 - 8 -> amem_range (p + 18) 32 ->
(forall x, p + 18 <= x < p + 50 -> ~ in_img SEGS x) ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->
(* the 32 bytes are in the caller's machine stack, above this call's sp and
   inside the caller's window: AR marks the whole machine stack usable in every
   state (lib/Reusable/YG0n.v:188-191), which is what keeps them usable across
   the frame this call takes on the side stack for frames *)
spZ regs <= p + 18 -> p + 50 <= sp0 ->
(* the three argument bytes it copies in, which lie in a frame of the caller's
   on the side stack for frames, whose bytes and shadow the frame this call
   takes leaves alone *)
g <> 0 -> tsrc_ok W memc (spZ regs) g 3 ->
garr8 SEGS (mrestrict (w_H W) memc) g [ch; pm; v] ->
afobj SEGS B lyc Sc W memc g 3 ->
(p + 50 <= g \/ g + 3 <= p + 18) ->
SRr SEGS W (cfg_at SEGS a regs memc mdc)
(tlay_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p ch pm v).
End e.
End d.
End b.
