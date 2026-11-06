(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase ADepot_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 AModelFacts F_apoison F_aalloc_s F_aalloc1 F_aalloc2 F_aalloc3.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma poison_cells_frame_b : forall m m' W,
poison_cells m -> munch W m m' -> wmono bsegs m m' ->
Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> poison_cells m'.
Proof.
intros m m' W PC MU WM HW.
assert (D : forall A n, AIMG_LO <= A -> A + n <= AIMG_HI -> disjoint_from W A n).
{ intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
unfold poison_cells, AIMG_HI, AIMG_LO in *.
destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.
#[using="Type"] Lemma lt_pow2_of_log2 : forall a k, 0 <= a -> Z.log2 a < k -> a < 2 ^ k.
Proof.
intros a k Ha Hl. destruct (Z.eq_dec a 0) as [->|]. { cbn in Hl. Local Ltac2 Set LiaHints.tbl := fun () => "0060=41415986077.44686355236.8 51794598124.451796577670.851796692231.759314873579.900000100400800;00A00GSS1GS2HlS1KS2Hl1HS2Hl1H".
apply Z.pow_pos_nonneg; lia. }
assert (K : 0 <= k) by (pose proof (Z.log2_nonneg a); lia).
destruct (Z.lt_ge_cases a (2 ^ k)) as [L|G]; [exact L|]. exfalso.
assert (k <= Z.log2 a). { rewrite <- (Z.log2_pow2 k) by lia. apply Z.log2_le_mono. lia. } lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hdr_b1_mid_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid b1 < 256.
Proof.
intros b1 Hb. unfold hdr_b1_mid.
set (x := Z.lor (Z.land b1 18446744073709551612) 1).
Local Ltac2 Set LiaHints.tbl := fun () => "0080=21729222224.650071946878.750653792827.362997561758.662997709214.565502300846.66755913196.3 68106533001.600000400800<00=00>00?00@00DS2A0S2L1S2HbSSSSS2A0".
assert (X0 : 0 <= x) by (subst x; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
assert (A0 : 0 <= Z.land x 143) by (apply Z.land_nonneg; right; lia).
split. { apply Z.lor_nonneg. lia. }
change 256 with (2^8). apply lt_pow2_of_log2. { apply Z.lor_nonneg; lia. }
rewrite Z.log2_lor by lia.
pose proof (Z.log2_land x 143 X0 ltac:(lia)) as L1.
replace (Z.log2 143) with 7 in L1 by reflexivity. replace (Z.log2 16) with 4 by reflexivity. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.
End WithDepot.
End CANSEC2.
