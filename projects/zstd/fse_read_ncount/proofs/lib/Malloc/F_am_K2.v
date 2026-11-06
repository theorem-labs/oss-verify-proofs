(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_A2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Module A2 := MallocKit_A2.
Section CANSEC1. Context {rc : runConstT}.
Definition clear_range (st : mstate) (lo n : Z) : Prop :=
forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).
#[using="Type"] Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>59314873579.1300000:S2Hx3Hin1H".
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). Local Ltac2 Set LiaHints.tbl := fun () => "0020>17208403286.3 63109864048.1700000100=SS1H2H02H12H5".
rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= ATOP.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.
Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.
End GROW.
End CANSEC1.
