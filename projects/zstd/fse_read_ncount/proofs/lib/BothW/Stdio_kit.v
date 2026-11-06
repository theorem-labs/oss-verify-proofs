(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Export Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
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
Definition FMT_FP_DEPTH : Z := 4640.
Definition ICPT_DEPTH : Z := 2240.
#[using="Type"] Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.
Definition ashenv (m : word -> option byte) : Prop :=
rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m
/\ rt_real_printf m /\ rt_real_wcslen m /\ rt_real_read m
/\ rw_cells bsegs m 0x9b650 [C8 (Z_to_bv 64 0x8f1f8)]
/\ rw_cells bsegs m 0x9b720 [C8 (Z_to_bv 64 0x934cc)]
/\ rw_cells bsegs m 0x9b638 [C8 (Z_to_bv 64 0x92b44)]
/\ rw_cells bsegs m 0x1340b8 [C8 (Z_to_bv 64 4294967296)]
/\ rw_cells bsegs m 0x134160 [C8 (Z_to_bv 64 0x101010101010101)].
Definition ashsafe (W : list (Z * Z)) : Prop :=
disjoint_from W 0x99900 48 /\ disjoint_from W 0x9a478 8 /\ disjoint_from W 0x9b770 16
/\ disjoint_from W 0xa2538 8 /\ disjoint_from W 0xa3218 2 /\ disjoint_from W 0xa3220 24
/\ disjoint_from W 0x9b668 16 /\ disjoint_from W 0x9b720 8 /\ disjoint_from W 0x9b648 8
/\ disjoint_from W 0x9b650 8 /\ disjoint_from W 0x9b720 8 /\ disjoint_from W 0x9b638 8
/\ disjoint_from W 0x1340b8 8 /\ disjoint_from W 0x134160 8.
#[using="Type"] Lemma ashenv_transport : forall W m m', ashenv m -> munch W m m' -> wmono bsegs m m' -> ashsafe W -> ashenv m'.
Proof.
intros W m m' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14) MU WM
(D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
unfold ashenv. repeat lazymatch goal with |- _ /\ _ => split; [eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; assumption] |] end.
eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; assumption].
Qed.
#[using="Type"] Lemma ashenv_core : forall m, ashenv m -> rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m.
Proof. intros m (A1 & A2 & A3 & A4 & A5 & A6 & _). exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 A6))))). Qed.
#[using="Type"] Lemma ashsafe_cons_high : forall lo hi W, 0x134168 <= lo -> ashsafe W -> ashsafe ((lo, hi) :: W).
Proof. intros lo hi W H D. unfold ashsafe in *; cbn [disjoint_from]. repeat split; try apply D; lia. Qed.
#[using="Type"] Lemma ashsafe_cons_file : forall lo hi W, 0x9b780 <= lo -> hi <= 0xa2538 -> ashsafe W -> ashsafe ((lo, hi) :: W).
Proof. intros lo hi W H1 H2 D. unfold ashsafe in *; cbn [disjoint_from]. repeat split; try apply D; lia. Qed.
#[using="Type"] Lemma ashsafe_nil : ashsafe [].
Proof. repeat split. Qed.
Definition hull64 (lo hi RLO RHI : Z) : Prop :=
RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND.
Definition shclean (m : word -> option byte) (lo hi RLO RHI : Z) : Prop :=
unpoisoned m lo hi /\ hull64 lo hi RLO RHI /\ wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ app_blk lo hi.
#[using="Type"] Lemma shclean_sub : forall m lo hi RLO RHI lo' hi',
shclean m lo hi RLO RHI -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> shclean m lo' hi' RLO RHI.
Proof.
intros m lo hi RLO RHI lo' hi' (U & (H1 & H2 & H3) & W & AB) Hlo Hm Hhi. split; [| split; [| split; [exact W|]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "0030>44426045396.1747995169047.1750842374085.1700000B00G00LS2H12H22H33Hlo3HhiS3HloS3Hhi".
eapply unpoisoned_sub; [exact U| lia| lia].
- unfold hull64 in *. lia.
- eapply app_blk_sub; eauto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shclean_hull : forall m lo hi RLO RHI, shclean m lo hi RLO RHI ->
RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND.
Proof. intros m lo hi RLO RHI (_ & H & _). exact H. Qed.
#[using="Type"] Lemma shclean_app_blk : forall m lo hi RLO RHI, shclean m lo hi RLO RHI -> app_blk lo hi.
Proof. intros m lo hi RLO RHI (_ & _ & _ & H). exact H. Qed.
#[using="Type"] Lemma shclean_transport : forall W m m' lo hi RLO RHI,
shclean m lo hi RLO RHI -> munch W m m' -> wmono bsegs m m' ->
disjoint_from W (shad RLO) (shad RHI - shad RLO) -> lo < hi ->
shclean m' lo hi RLO RHI.
Proof.
intros W m m' lo hi RLO RHI (U & H & WR & AB) MU WM D LT. split; [| split; [exact H| split; [eapply wr_at_transport; eauto| exact AB]]].
eapply unpoisoned_munch; [exact U| exact MU|].
destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
Local Ltac2 Set LiaHints.tbl := fun () => "0030>20435432310.1231786401968.2149325812778.5000000:00>00VS2S12S22D1S2H1S2H22H41H2H03H103H113H15".
assert (S1 : shad RLO <= shad lo) by (apply shad_mono; lia).
assert (S2 : shad (hi - 1) + 1 <= shad RHI).
{ rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
revert D. clear - S1 S2. induction W as [|[a b] W IH]; cbn [disjoint_from]; [auto|].
intros [D1 D2]. split; [lia| apply IH; exact D2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition appW (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= KLOW \/ KHIGH <= fst iv) W.
#[using="Type"] Lemma appW_shadow_disjoint : forall W RLO RHI, appW W -> 0 <= RLO -> RHI <= KEND ->
disjoint_from W (shad RLO) (shad RHI - shad RLO).
Proof.
intros W RLO RHI HW H0 H1. induction HW as [|[a b] W Hab HW IH]; cbn [disjoint_from]; [exact I|].
cbn [fst snd] in Hab. split; [| exact IH].
rewrite !shad_div. unfold ASHOFF, KLOW, KHIGH, KEND in *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68278300139.2500000FS3Hab2H02H11H2H22H62H7".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shclean_transport_app : forall W m m' lo hi RLO RHI,
shclean m lo hi RLO RHI -> munch W m m' -> wmono bsegs m m' -> appW W -> lo < hi -> shclean m' lo hi RLO RHI.
Proof.
intros W m m' lo hi RLO RHI SH MU WM HW LT. pose proof (shclean_hull _ _ _ _ _ SH) as (_ & _ & _ & _ & H0 & H1).
eapply shclean_transport; eauto. apply appW_shadow_disjoint; auto.
Qed.
#[using="Type"] Lemma appW_cons : forall a b W, (b <= KLOW \/ KHIGH <= a) -> appW W -> appW ((a, b) :: W).
Proof. intros a b W H HW. constructor; [exact H| exact HW]. Qed.
#[using="Type"] Lemma appW_nil : appW []. Proof. constructor. Qed.
Record region := mkRegion { r_lo : Z; r_hi : Z; r_rlo : Z; r_rhi : Z }.
Definition rclean (m : word -> option byte) (r : region) : Prop :=
shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r) /\ r_lo r < r_hi r.
Definition rrng (RNG : footprint) (r : region) : Prop := rng RNG (shad (r_rlo r)) (shad (r_rhi r) - shad (r_rlo r)).
Definition inreg (r : region) (a n : Z) : Prop := r_lo r <= a /\ a + n <= r_hi r.
#[using="Type"] Lemma rclean_transport : forall W m m' r,
rclean m r -> munch W m m' -> wmono bsegs m m' -> appW W -> rclean m' r.
Proof. intros W m m' r [SH LT] MU WM HW. split; [| exact LT]. eapply shclean_transport_app; eauto. Qed.
#[using="Type"] Lemma rclean_shclean : forall m r, rclean m r -> shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r).
Proof. intros m r [H _]; exact H. Qed.
#[using="Type"] Lemma rclean_lt : forall m r, rclean m r -> r_lo r < r_hi r.
Proof. intros m r [_ H]; exact H. Qed.
#[using="Type"] Lemma inreg_sub : forall r a n a' n', inreg r a n -> a <= a' -> a' + n' <= a + n -> inreg r a' n'.
Proof. unfold inreg. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010=44029067110.9000009S1H2H02H1".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition RBstdout : region := mkRegion 0x5f5be0 0x5f5fe0 0x5f5bc0 0x5f6000.
End CANSEC1.
Ltac solve_ashsafe :=
repeat first [ apply ashsafe_nil
| apply ashsafe_cons_high; [unfold KHIGH in *; lia|]
| apply ashsafe_cons_file; [lia| lia|]
|
unfold ashsafe; cbn [disjoint_from]; unfold KHIGH in *; repeat split; lia ].
Ltac solve_appW :=
repeat first [ apply appW_nil
| apply appW_cons; [unfold KLOW, KHIGH in *; cbn [fst snd]; first [lia | left; lia | right; lia] |] ].
Tactic Notation "xport_env" constr(ENV) constr(MU) constr(WM) "as" ident(X) :=
pose proof (ashenv_transport _ _ _ ENV MU WM ltac:(solve_ashsafe)) as X.
Tactic Notation "xport_reg" constr(RC) constr(MU) constr(WM) "as" ident(X) :=
pose proof (rclean_transport _ _ _ _ RC MU WM ltac:(solve_appW)) as X.
