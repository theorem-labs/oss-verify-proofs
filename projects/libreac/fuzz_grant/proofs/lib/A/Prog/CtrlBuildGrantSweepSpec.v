(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACe6.v, proofs/cgif/cgif_file_fuzzer/lib/YC20.v. *)
(* The contract of reac_ctrl_build_grant_sweep (0x82d8c) on fuzz_grant's ASan
   build — the statement only; the walk that proves it is CtrlBuildGrantSweep.v.
   A caller Requires this file and takes `tctrl_build_grant_sweep_spec` as a
   Section hypothesis, so its own file does not depend on the walk.

   The call fills the caller's row buffer `uint8_t sweep[][34]` with the
   enrolment burst, Pau's SWEEP base w vals (lib/Prog/GrantSweepModel.v:62-64),
   when every argument is one the burst can carry (bgs_ok), and otherwise
   returns -1 having written nothing. It writes the caller's buffer, so the
   contract is in the caller-journal form (cgif lib/YC20.v:311-365); tcj_kept,
   twr_ok and tsrc_ok are CtrlFinish.v's. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import CtrlLayBlockSpec CtrlStampHeadampSpec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
Definition A_ACK : nat := 20%nat.      (* GRANT_HEAD_ACK,  0x211c0, 34 bytes *)
Definition A_MARK : nat := 21%nat.     (* GRANT_HEAD_MARK, 0x21220, 34 bytes *)
Definition A_GB : nat := 19%nat.       (* GRANT_GROUPB,    0x21040, 204 bytes *)
(* its own frame (1632) plus the deepest callee's stack *)
Definition TBGS_STK : Z := 1632 + TSTAMP_STK.
Definition EV_BGS : Z := EV_STAMP.
(* the number of rows the burst holds for a width w *)
Definition sweep_rows (w : Z) : Z := 8 + 3 * w.
(* the call lays rows down only when every argument is one the burst can carry *)
Definition bgs_ok (s V mx base w : Z) : Prop :=
s <> 0 /\ V <> 0 /\ 1 <= w /\ base + w <= 48 /\ sweep_rows w <= mx.
Section e.
Variable B : asyms.
Definition tbgs_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (s mx base w V : Z) (vals : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_BGS) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
(exists f, S2 = set_fs f Sc) /\
getr regs2 10 = w64 res /\
tcj_kept B TBGS_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => bgs_ok s V mx base w /\ s <= a < s + 34 * sweep_rows w) /\
(bgs_ok s V mx base w /\ res = sweep_rows w /\
garr8 SEGS (mrestrict (w_H W2) mem2) s (map bv_unsigned (SWEEP base (Z.to_nat w) vals))
\/ ~ bgs_ok s V mx base w /\ res = -1 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - TBGS_STK <= a < spZ regs) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i))).
Definition tctrl_build_grant_sweep_spec (a : Z) (rlo rhi : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s mx base w V : Z)
(vals : list byte) cl,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS rlo rhi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 s -> getr regs 11 = w64 mx -> getr regs 12 = w64 base ->
getr regs 13 = w64 w -> getr regs 14 = w64 V ->
0 <= s < 2 ^ 63 -> - 2 ^ 31 <= mx < 2 ^ 31 -> 0 <= base < 256 -> - 2 ^ 31 <= w < 2 ^ 31 -> 0 <= V < 2 ^ 63 ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) cl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TBGS_STK -> spZ regs <= sp0 ->
Z.of_nat (length (frames Sc)) <= 8 ->
(* the values the caller hands in *)
(1 <= w -> V <> 0 ->
length vals = Z.to_nat (3 * w) /\ vals_legal (Z.to_nat w) vals /\
garr8 SEGS (mrestrict (w_H W) memc) V (map bv_unsigned vals) /\
tsrc_ok W memc (spZ regs) V (3 * w) /\
(* the values live in a frame the caller took on the side stack for frames, so
   they and their shadow survive the calls this one makes *)
afobj SEGS B lyc Sc W memc V (3 * w) /\
(spZ regs <= V \/ V + 3 * w <= spZ regs - TBGS_STK)) ->
(* the row buffer, only when the burst is laid down *)
(bgs_ok s V mx base w ->
amem_range s (34 * sweep_rows w) /\ s + 34 * sweep_rows w <= 2 ^ 47 - 8 /\
(forall x, s <= x < s + 34 * sweep_rows w -> ~ in_img SEGS x) /\
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) s (34 * sweep_rows w) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s (34 * sweep_rows w) /\
shadow_hull_vis (aview SEGS (w_H W) memc) s (34 * sweep_rows w) /\
(* the rows live in one block of the caller's, so a row written before a call
   is still there after it, and the shadow says so again *)
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 34 * sweep_rows w <= b + req_size m) /\
(spZ regs <= s \/ s + 34 * sweep_rows w <= spZ regs - TBGS_STK) /\
(V + 3 * w <= s \/ s + 34 * sweep_rows w <= V)) ->
SRr SEGS W (cfg_at SEGS a regs memc mdc)
(tbgs_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
End e.
End d.
End b.
