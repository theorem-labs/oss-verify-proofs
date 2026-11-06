(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACe6.v. *)
(* The contract of reac_ctrl_stamp_headamp (0x82a14) on fuzz_grant's ASan build
   — the statement only; the walk that proves it is CtrlStampHeadamp.v. A caller
   Requires this file and takes `tctrl_stamp_headamp_spec` as a Section
   hypothesis, so its own file does not depend on the walk.

   It refuses a head-amp parameter/value pair the console cannot carry
   (legalb) and otherwise lays the control block over the caller's bytes
   [p+16, p+50): the type word 0xcd 0xea, then ctrl_lay_block and ctrl_finish.
   The result is Pau's GAz ch pm v (lib/Prog/GrantSweepModel.v:38-40). It
   writes the caller's bytes, so the contract is in the caller-journal form
   (cgif lib/YC20.v:311-365); tcj_kept and twr_ok are CtrlFinish.v's. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import CtrlLayBlockSpec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
(* its own frame (96) plus the 32 bytes `andi sp,sp,-32` at 0x82a4c may drop,
   plus the deepest callee's stack (ctrl_lay_block's; ctrl_finish needs less). *)
Definition TSTAMP_STK : Z := 128 + TLAY_STK.
Definition EV_STAMP : Z := EV_LAY.
Section e.
Variable B : asyms.
Definition tstamp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (p ch pm v : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_STAMP) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
(exists f, S2 = set_fs f Sc) /\
getr regs2 10 = w64 res /\
tcj_kept B TSTAMP_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => p + 16 <= a < p + 50) /\
(if legalb pm v
then res = 0 /\ garr8 SEGS (mrestrict (w_H W2) mem2) (p + 16) (GAz ch pm v)
else res = -1 /\ (forall a, p + 16 <= a < p + 50 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a)).
Definition tctrl_stamp_headamp_spec (a : Z) (rlo rhi : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p ch pm v : Z) cl,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS rlo rhi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 p -> getr regs 11 = w64 ch -> getr regs 12 = w64 pm -> getr regs 13 = w64 v ->
0 <= ch < 256 -> 0 <= pm < 256 -> 0 <= v < 256 ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) cl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TSTAMP_STK -> spZ regs <= sp0 ->
Z.of_nat (length (frames Sc)) <= 8 ->
(* the 34 bytes it stamps, only when it accepts the pair *)
0 <= p -> p + 50 <= 2 ^ 47 - 8 -> amem_range (p + 16) 34 ->
(forall x, p + 16 <= x < p + 50 -> ~ in_img SEGS x) ->
(* the caller's bytes are in its own machine stack, above this call's sp and
   inside the caller's window, so AR marks them usable in every state and the
   callees' own stack never reaches them *)
spZ regs <= p + 16 -> p + 50 <= sp0 ->
(legalb pm v = true ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 16) 34) ->
SRr SEGS W (cfg_at SEGS a regs memc mdc)
(tstamp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p ch pm v).
End e.
End d.
End b.
