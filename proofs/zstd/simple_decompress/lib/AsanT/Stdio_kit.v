(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Export Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition FMT_FP_DEPTH : Z := 4640.
Definition fmt_fp_entry : Z := 0xbe060.

(* [comment removed for export] *)
Definition ICPT_DEPTH : Z := 2240.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ashenv (m : word -> option byte) : Prop :=
  rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m
  (* [comment removed for export] *)
  /\ rt_real_printf m /\ rt_real_wcslen m /\ rt_real_read m
  /\ rw_cells bsegs m 0xc9090 [C8 (Z_to_bv 64 0xbcbf0)]
  /\ rw_cells bsegs m 0xc9160 [C8 (Z_to_bv 64 0xc0ec4)]
  /\ rw_cells bsegs m 0xc9078 [C8 (Z_to_bv 64 0xc053c)]
  /\ rw_cells bsegs m 0x161878 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells bsegs m 0x161920 [C8 (Z_to_bv 64 0x101010101010101)].

(* [comment removed for export] *)
Definition ashsafe (W : list (Z * Z)) : Prop :=
  disjoint_from W 0xc72f8 48 /\ disjoint_from W 0xc7e70 8 /\ disjoint_from W 0xc91b0 16
  /\ disjoint_from W 0xcfcf8 8 /\ disjoint_from W 0xd09d8 2 /\ disjoint_from W 0xd09e0 24
  /\ disjoint_from W 0xc90a8 16 /\ disjoint_from W 0xc9160 8 /\ disjoint_from W 0xc9088 8
  /\ disjoint_from W 0xc9090 8 /\ disjoint_from W 0xc9160 8 /\ disjoint_from W 0xc9078 8
  /\ disjoint_from W 0x161878 8 /\ disjoint_from W 0x161920 8.

Lemma ashenv_transport : forall W m m', ashenv m -> munch W m m' -> wmono bsegs m m' -> ashsafe W -> ashenv m'.
Proof.
  intros W m m' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14) MU WM
         (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
  unfold ashenv. repeat lazymatch goal with |- _ /\ _ => split; [eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; assumption] |] end.
  eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; assumption].
Qed.

(* [comment removed for export] *)
Lemma ashenv_core : forall m, ashenv m -> rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m.
Proof. intros m (A1 & A2 & A3 & A4 & A5 & A6 & _). exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 A6))))). Qed.

(* [comment removed for export] *)
Lemma ashsafe_cons_high : forall lo hi W, 0x161928 <= lo -> ashsafe W -> ashsafe ((lo, hi) :: W).
Proof. intros lo hi W H D. unfold ashsafe in *; cbn [disjoint_from]. repeat split; try apply D; lia. Qed.
Lemma ashsafe_cons_file : forall lo hi W, 0xc91c0 <= lo -> hi <= 0xcfcf8 -> ashsafe W -> ashsafe ((lo, hi) :: W).
Proof. intros lo hi W H1 H2 D. unfold ashsafe in *; cbn [disjoint_from]. repeat split; try apply D; lia. Qed.
Lemma ashsafe_nil : ashsafe [].
Proof. repeat split. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hull64 (lo hi RLO RHI : Z) : Prop :=
  RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND.

Definition shclean (m : word -> option byte) (lo hi RLO RHI : Z) : Prop :=
  unpoisoned m lo hi /\ hull64 lo hi RLO RHI /\ wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ app_blk lo hi.

Lemma shclean_sub : forall m lo hi RLO RHI lo' hi',
  shclean m lo hi RLO RHI -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> shclean m lo' hi' RLO RHI.
Proof.
  intros m lo hi RLO RHI lo' hi' (U & (H1 & H2 & H3) & W & AB) Hlo Hm Hhi. split; [| split; [| split; [exact W|]]].
  - eapply unpoisoned_sub; [exact U| lia| lia].
  - unfold hull64 in *. lia.
  - eapply app_blk_sub; eauto.
Qed.

Lemma shclean_hull : forall m lo hi RLO RHI, shclean m lo hi RLO RHI ->
  RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND.
Proof. intros m lo hi RLO RHI (_ & H & _). exact H. Qed.
Lemma shclean_unpoisoned : forall m lo hi RLO RHI, shclean m lo hi RLO RHI -> unpoisoned m lo hi.
Proof. intros m lo hi RLO RHI (H & _). exact H. Qed.
Lemma shclean_wr : forall m lo hi RLO RHI, shclean m lo hi RLO RHI -> wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
Proof. intros m lo hi RLO RHI (_ & _ & H & _). exact H. Qed.
Lemma shclean_app_blk : forall m lo hi RLO RHI, shclean m lo hi RLO RHI -> app_blk lo hi.
Proof. intros m lo hi RLO RHI (_ & _ & _ & H). exact H. Qed.

(* [comment removed for export] *)
Lemma shclean_transport : forall W m m' lo hi RLO RHI,
  shclean m lo hi RLO RHI -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W (shad RLO) (shad RHI - shad RLO) -> lo < hi ->
  shclean m' lo hi RLO RHI.
Proof.
  intros W m m' lo hi RLO RHI (U & H & WR & AB) MU WM D LT. split; [| split; [exact H| split; [eapply wr_at_transport; eauto| exact AB]]].
  eapply unpoisoned_munch; [exact U| exact MU|].
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (S1 : shad RLO <= shad lo) by (apply shad_mono; lia).
  assert (S2 : shad (hi - 1) + 1 <= shad RHI).
  { rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  revert D. clear - S1 S2. induction W as [|[a b] W IH]; cbn [disjoint_from]; [auto|].
  intros [D1 D2]. split; [lia| apply IH; exact D2].
Qed.

(* [comment removed for export] *)
Lemma shclean_empty : forall m lo RLO RHI,
  hull64 lo lo RLO RHI -> wr_at bsegs m (shad RLO) (shad RHI - shad RLO) -> app_blk lo lo -> shclean m lo lo RLO RHI.
Proof.
  intros m lo RLO RHI H W AB. split; [| split; [exact H| split; [exact W| exact AB]]].
  destruct H as (H1 & H2 & _ & _ & H5 & H6). unfold KEND in H6.
  apply unpoisoned_nil. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition appW (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= KLOW \/ KHIGH <= fst iv) W.

Lemma appW_shadow_disjoint : forall W RLO RHI, appW W -> 0 <= RLO -> RHI <= KEND ->
  disjoint_from W (shad RLO) (shad RHI - shad RLO).
Proof.
  intros W RLO RHI HW H0 H1. induction HW as [|[a b] W Hab HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst snd] in Hab. split; [| exact IH].
  rewrite !shad_div. unfold ASHOFF, KLOW, KHIGH, KEND in *. Z.div_mod_to_equations. lia.
Qed.

Lemma shclean_transport_app : forall W m m' lo hi RLO RHI,
  shclean m lo hi RLO RHI -> munch W m m' -> wmono bsegs m m' -> appW W -> lo < hi -> shclean m' lo hi RLO RHI.
Proof.
  intros W m m' lo hi RLO RHI SH MU WM HW LT. pose proof (shclean_hull _ _ _ _ _ SH) as (_ & _ & _ & _ & H0 & H1).
  eapply shclean_transport; eauto. apply appW_shadow_disjoint; auto.
Qed.

Lemma appW_cons : forall a b W, (b <= KLOW \/ KHIGH <= a) -> appW W -> appW ((a, b) :: W).
Proof. intros a b W H HW. constructor; [exact H| exact HW]. Qed.
Lemma appW_nil : appW []. Proof. constructor. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region := mkRegion { r_lo : Z; r_hi : Z; r_rlo : Z; r_rhi : Z }.

(* [comment removed for export] *)
Definition rclean (m : word -> option byte) (r : region) : Prop :=
  shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r) /\ r_lo r < r_hi r.
(* [comment removed for export] *)
Definition rrng (RNG : footprint) (r : region) : Prop := rng RNG (shad (r_rlo r)) (shad (r_rhi r) - shad (r_rlo r)).
(* [comment removed for export] *)
Definition inreg (r : region) (a n : Z) : Prop := r_lo r <= a /\ a + n <= r_hi r.

Lemma rclean_transport : forall W m m' r,
  rclean m r -> munch W m m' -> wmono bsegs m m' -> appW W -> rclean m' r.
Proof. intros W m m' r [SH LT] MU WM HW. split; [| exact LT]. eapply shclean_transport_app; eauto. Qed.

Lemma rclean_shclean : forall m r, rclean m r -> shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r).
Proof. intros m r [H _]; exact H. Qed.
Lemma rclean_lt : forall m r, rclean m r -> r_lo r < r_hi r.
Proof. intros m r [_ H]; exact H. Qed.
Lemma inreg_sub : forall r a n a' n', inreg r a n -> a <= a' -> a' + n' <= a + n -> inreg r a' n'.
Proof. unfold inreg. intros. lia. Qed.

(* [comment removed for export] *)
Definition RBstdout : region := mkRegion 0x6233c0 0x6237c0 0x623380 0x623800.
Example RBstdout_hull64 : 0x623380 mod 64 = 0 /\ 0x623800 mod 64 = 0 /\ 0x623380 <= 0x6233c0 /\ 0x6237c0 <= 0x623800. Proof. repeat split; first [reflexivity | lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End CANSEC1.
Ltac solve_ashsafe :=
  repeat first [ apply ashsafe_nil
               | apply ashsafe_cons_high; [unfold KHIGH in *; lia|]
               | apply ashsafe_cons_file; [lia| lia|]
               | (* [comment removed for export] *)
                 unfold ashsafe; cbn [disjoint_from]; unfold KHIGH in *; repeat split; lia ].
Ltac solve_appW :=
  repeat first [ apply appW_nil
               | apply appW_cons; [unfold KLOW, KHIGH in *; cbn [fst snd]; first [lia | left; lia | right; lia] |] ].

(* [comment removed for export] *)
Tactic Notation "xport_env" constr(ENV) constr(MU) constr(WM) "as" ident(X) :=
  pose proof (ashenv_transport _ _ _ ENV MU WM ltac:(solve_ashsafe)) as X.
(* [comment removed for export] *)
Tactic Notation "xport_reg" constr(RC) constr(MU) constr(WM) "as" ident(X) :=
  pose proof (rclean_transport _ _ _ _ RC MU WM ltac:(solve_appW)) as X.
